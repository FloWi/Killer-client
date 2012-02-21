package de.tdng2011.game.killerclient

import de.tdng2011.game.library.util.{ByteUtil,Vec2}
import actors.Actor
import de.tdng2011.game.library.connection.{RelationTypes, AbstractClient}
import de.tdng2011.game.library.{ScoreBoard, World, EntityTypes,Player,Shot}
import scala.math.{asin,atan,abs,acos}

class Client(hostname : String,myName:String) extends AbstractClient(hostname, RelationTypes.Player) {

	val worldSize=1000
	val shotRadius=5
	val shotSpeed=400
	val Pi=3.1415927
	val magicShotId= -666

	val framesPerSecond = 40.0
	val frameDuration = 1.0/framesPerSecond

	val lookAheadTime=2

	val simTime    =1.0
	val simShotTime=0.8

	case class VVV(v:Vec2) extends Vec2(v.x, v.y) {
		private def fix(a:Float) = ((a%worldSize)+worldSize)%worldSize
		private def fix2(a:Float) = if (a < - worldSize /2 ) a+worldSize else if (a > worldSize /2 ) a-worldSize else a

		def norm = Vec2(fix(x), fix(y))
		def normDelta = Vec2(fix2(x), fix2(y))
		def dist(v:Vec2) : Float = VVV(this - v).normDelta.length.floatValue
	}

	case class SimEnt(
		var pos:Vec2, 
		var publicId:Long, 
		var speed:Double, 
		var radius:Double, 
		var direction:Double, 
		var rotSpeed:Double,
		var turnLeft:Boolean,
		var turnRight:Boolean,
		var thrust:Boolean) {

		var alive=true

		def step(time:Double) {
			if (turnLeft) direction -= (time * rotSpeed).floatValue
			if (turnRight) direction += (time * rotSpeed).floatValue
			direction %= 2 * Pi.floatValue
			if (direction < 0) direction += 2 * Pi.floatValue

			val len = time * speed
			val step = if (thrust) Vec2(1, 0).rotate(direction.toFloat) * len.floatValue else Vec2(0,0)
			pos=VVV(pos + step).norm
		}

		def collidesWith(ent:SimEnt):Boolean={
			if (ent.publicId==publicId || !ent.alive || !alive)
				false
			else {
				val (p1,p2) = fixTurnAround(ent.pos,pos)
				(p1-p2).length<ent.radius+radius
			}
		}
				
	}
		
	class SimWorld(w:World,var b:Behavior,me:Player) {
		var ents:IndexedSeq[SimEnt]=IndexedSeq()

		//ctor:
		val count=w.shots.length+w.players.length
		w.players.foreach(p=>ents = ents :+ SimEnt(p.pos,p.publicId,p.speed,p.radius,p.direction,p.rotSpeed,p.turnLeft,p.turnRight,p.thrust))
		w.shots.foreach  (s=>ents = ents :+ SimEnt(s.pos,s.publicId,s.speed,s.radius,s.direction,0,false,false,true))

		if (b.shot) {
			val shotPos = me.pos + Vec2(1, 0).rotate(me.direction)* (me.radius + shotRadius)
			ents = ents :+ SimEnt(shotPos,magicShotId, shotSpeed,shotRadius, me.direction,0,false,false,true)
		}

		def step(time:Double) { ents.foreach(e=>e.step(time)) }

		def checkCollisions(id:Long):Boolean = {
			val me=ents.find(_.publicId==id)
			if (me.isEmpty) 
				false
			else
				ents.map(x=>x.collidesWith(me.get)).reduceLeft(_|_)
		}

		def checkShotCollisions(id:Long) : Boolean = {
			val shot=ents.find(_.publicId==id)
			var ret=false
			if (!shot.isEmpty) ents.foreach(x=> if (x.collidesWith(shot.get)) { shot.get.alive=false; x.alive=false; ret=true } )
			ret
		}

		def simulate(time:Double,playerId:Long,shotId:Long):Behavior={
			var t:Double=0
			var amIDead=false
			val me=ents.find(_.publicId==playerId)
			if (me.isEmpty) {
				b.setSurvivalTime(0)	
			}
			else {
				b.applyTo(me.get)

				while (t<time && !amIDead) {
					step(frameDuration)
					amIDead=checkCollisions(playerId)
					val old=b.shotHasHit
					b.shotHasHit|=checkShotCollisions(shotId)
					if (b.shotHasHit && !old) b.shotHasHitTime=t
					if (!amIDead) t=t+frameDuration
				}
				b.setSurvivalTime(t)
			}
		}

	}

	case class Behavior(val turnLeft:Boolean,val turnRight:Boolean, val thrust:Boolean, val shot:Boolean) {
		var shotHasHit=false
		var survivalTime=0.0
		var shotHasHitTime=8888.0

		def applyTo(p:SimEnt):Behavior = {
			p.turnLeft=turnLeft
			p.turnRight=turnRight
			p.thrust=thrust
			this
		}
		def setSurvivalTime(t:Double):Behavior = {
			survivalTime=t;
			this
		}
	}

	val minDistFactor=7

	override def name = myName

	var lastNextPos=Vec2(0,0)
	var lastCanShoot=true
	var lastNextPublicId:Long=0
	var lastSelfPos=Vec2(0,0)

	def norm(v:Vec2)={ 
		val l=v.length.floatValue 
		if (l==0) Vec2(1,0) else Vec2(v.x/l,v.y/l) 
	}

	def orto(v:Vec2) = new Vec2(v.y,-v.x)

	def fixTurnAround(a:Vec2, b:Vec2) = {
		def minFix(me:Float, you:Float) = if (me<you) me+worldSize else me
		def near(a:Float,b:Float) = abs(a-b) < worldSize/2

		def fixX( t:(Vec2,Vec2) ) = 
			if ( near(t._1.x,t._2.x) ) 
				(t._1,t._2) 
			else 
				( Vec2(minFix(t._1.x,t._2.x) , t._1.y) , Vec2(minFix(t._2.x,t._1.x) , t._2.y) )

		def fixY( t:(Vec2,Vec2) ) = 
			if ( near(t._1.y,t._2.y) ) 
				(t._1,t._2) 
			else 
				( Vec2(t._1.x , minFix(t._1.y,t._2.y)) , Vec2(t._2.x , minFix(t._2.y,t._1.y)) )

		fixX(fixY( (a,b) ))
	}
	
	def dist(a:Player, b:Player) = {
		val (apos,bpos)=fixTurnAround(a.pos,b.pos)
		(apos - bpos).length
	}

	def distShotToPlayer(a:Shot, b:Player) = {
		val (apos,bpos)=fixTurnAround(a.pos,b.pos)
		(apos - bpos).length
	}

	def getNext(self:Player)(a:Player,b:Player) = 
		if (a==self) b else 
		if (b==self) a else 
		if (dist(self,a) < dist(self,b)) a else b

	def getNextShot(self:Player)(a:Shot,b:Shot) = 
		if (a.parentId==self.publicId) b else
		if (b.parentId==self.publicId) a else
		if (distShotToPlayer(a,self) < distShotToPlayer(b,self)) a else b

	def findNextPlayer(world:World,self:Player) = world.players.reduceRight(getNext(self))

	def findNextShot(world:World,self:Player) :Option[Shot]= if (world.shots.length>0) Some(world.shots.reduceRight(getNextShot(self))) else None

	def radiantToVec2(radiant:Float) = norm(Vec2(1,0).rotate(radiant))
	def skalar(a:Vec2,b:Vec2) = a.x*b.x + a.y*b.y

	def calcGamma(s:Vec2, sd:Vec2, o:Vec2, od:Vec2) = 
		( o.y*sd.x - s.y*sd.x + s.x*sd.y - o.x*sd.y) / 
		( od.x*sd.y - od.y*sd.x)

	var maxD:Long=0
	var lastFrame:Long=0

	def processWorld(world : World) {
val frame=System.currentTimeMillis()
print("("+(frame-lastFrame)+")")
lastFrame=frame
val time=System.currentTimeMillis()
		val selfOpt=world.players.find(_.publicId==getPublicId)
		if (selfOpt.isEmpty) return
		val self      =selfOpt.get

		val shotOpt = world.shots.find(_.parentId==getPublicId)
		val canShoot = shotOpt.isEmpty
		val shotId   = if (shotOpt.isEmpty) -1 else shotOpt.get.publicId

		// ---------------------------- traditional code ------------------------
		val selfDir   =radiantToVec2(self.direction)
		
		val otherShot = findNextShot(world,self)

		val next = findNextPlayer(world,self)

		val nowPos    =next.pos
		val nowDir    =radiantToVec2(next.direction)

		val (nowNextPos,nowSelfPos) = fixTurnAround(next.pos,self.pos)
		val nowDist=(nowSelfPos-nowNextPos).length

		val eta=nowDist/shotSpeed

		val targetPosAtEta=nowPos + nowDir*(eta.floatValue * next.speed * (if (next.thrust) 1 else 0)) 

		val (targetPos,selfPos) = fixTurnAround(targetPosAtEta,self.pos)
		val dist      =(selfPos-targetPos).length

		val targetDir =radiantToVec2(next.direction)

		val delta     =norm(targetPos-selfPos)

		val cross     =selfDir.cross(delta)
		val alphaSin  =abs(asin(cross))
		val alphaCos  =abs(acos(skalar(selfDir,delta)))

		val beta      =atan((next.radius /* +shotRadius */ )/dist)
		val aim       =alphaSin<beta && alphaCos>0

		val left      =cross<0 
		val right     =cross>0 

		val isNear    =dist<self.radius*minDistFactor

		val ahead     = !isNear 

		lastNextPublicId=next.publicId
		lastNextPos=next.pos
		lastCanShoot=canShoot
		lastSelfPos=self.pos
var debug=""
		// --------------------------- no shot -------------------------------
		val l:List[Behavior]=List(
		  new SimWorld(world,Behavior(false,false,false,false),self).simulate(simTime,self.publicId,shotId) ,
		  new SimWorld(world,Behavior(true ,false,false,false),self).simulate(simTime,self.publicId,shotId) ,
		  new SimWorld(world,Behavior(false,true ,false,false),self).simulate(simTime,self.publicId,shotId) ,

		  new SimWorld(world,Behavior(false,false,true ,false),self).simulate(simTime,self.publicId,shotId) ,
		  new SimWorld(world,Behavior(true ,false,true ,false),self).simulate(simTime,self.publicId,shotId) ,
		  new SimWorld(world,Behavior(false,true ,true ,false),self).simulate(simTime,self.publicId,shotId) )

		val bestNoShot =l.reduceLeft( (a:Behavior,b:Behavior) => {
				if (a.survivalTime>b.survivalTime) 
					a
				else if (b.survivalTime>a.survivalTime)
					b
				else {
					var takeA=0
					if (a.turnLeft  && left)  takeA=takeA+1
					if (a.turnRight && right) takeA=takeA+1
					if (a.thrust    && ahead) takeA=takeA+1

					if (b.turnLeft  && left)  takeA=takeA-1
					if (b.turnRight && right) takeA=takeA-1
					if (b.thrust    && ahead) takeA=takeA-1

					if (takeA>0)
						a
					else
						b
				}
			})
		val worstNoShot=l.reduceLeft( (a:Behavior,b:Behavior) => if (a.survivalTime<b.survivalTime) a else b)

		var best=bestNoShot
		var letsPlayChess= worstNoShot.survivalTime<simTime && bestNoShot.survivalTime>simTime

if (letsPlayChess) debug=debug+"X "+worstNoShot.survivalTime+"  "
		// ---------------------------    shot -------------------------------
		
		if (canShoot) {
			val lns:List[Behavior]=List(
			  new SimWorld(world,Behavior(false,false,false,true),self).simulate(simShotTime,self.publicId,magicShotId) ,
			  new SimWorld(world,Behavior(true ,false,false,true),self).simulate(simShotTime,self.publicId,magicShotId) ,
			  new SimWorld(world,Behavior(false,true ,false,true),self).simulate(simShotTime,self.publicId,magicShotId) ,

			  new SimWorld(world,Behavior(false,false,true ,true),self).simulate(simShotTime,self.publicId,magicShotId) ,
			  new SimWorld(world,Behavior(true ,false,true ,true),self).simulate(simShotTime,self.publicId,magicShotId) ,
			  new SimWorld(world,Behavior(false,true ,true ,true),self).simulate(simShotTime,self.publicId,magicShotId) )

			val bestShot=lns.reduceLeft( (a:Behavior,b:Behavior) => {
				if (a.shotHasHit && !b.shotHasHit) 
					a
				else if (b.shotHasHit && !a.shotHasHit)
					b
				else if (a.survivalTime>b.survivalTime) 
					a
				else if (b.survivalTime>a.survivalTime)
					b
				else {
					var takeA=0
					if (a.turnLeft  && left)  takeA=takeA+1
					if (a.turnRight && right) takeA=takeA+1
					if (a.thrust    && ahead) takeA=takeA+1

					if (b.turnLeft  && left)  takeA=takeA-1
					if (b.turnRight && right) takeA=takeA-1
					if (b.thrust    && ahead) takeA=takeA-1

					if (takeA>0)
						a
					else
						b
				}
			})

			if (bestShot.survivalTime>bestNoShot.survivalTime) {
				best=bestShot
				letsPlayChess=true
if (letsPlayChess) debug=debug+"* "
			}

			if (bestShot.shotHasHit /* ************************ && bestShot.survivalTime >= bestNoShot.survivalTime*/) {
				best=bestShot
				letsPlayChess=true
if (letsPlayChess) debug=debug+"! "
			}
		}


// println(debug)


		if (letsPlayChess) {
			action(best.turnLeft && !best.shot,best.turnRight && !best.shot,best.thrust,best.shot)
if (best.shot && canShoot) print("*") else print(".")
		}
		else {
			action(left,right,ahead,false)
print(" ")
		}

val d=System.currentTimeMillis()-time
if (d>maxD) maxD=d
println(maxD+" "+d)
	}
}
