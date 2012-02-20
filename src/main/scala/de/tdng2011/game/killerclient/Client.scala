package de.tdng2011.game.killerclient

import de.tdng2011.game.library.util.{ByteUtil,Vec2}
import actors.Actor
import de.tdng2011.game.library.connection.{RelationTypes, AbstractClient}
import de.tdng2011.game.library.{ScoreBoard, World, EntityTypes,Player,Shot}
import scala.math.{asin,atan,abs,acos}

/*
object Shot {
  val defaultRadius   = 5.shortValue
  val defaultSpeed    = (Player.defaultSpeed * 4).shortValue // m/s
  val defaultLifeTime = World.size/defaultSpeed.asInstanceOf[Float]*0.5f
}

object Player {
  val defaultDirection        = 2.0f
  val defaultRadius           = 15.shortValue
  val defaultSpeed            = 100.shortValue // m/s
  val defaultRotSpeed : Float = 2*Pi.floatValue //rad/s
}
*/

class Client(hostname : String,myName:String) extends AbstractClient(hostname, RelationTypes.Player) {
	
	/*
	case class Mat2(var v11:Double,var v12:Double,var v21:Double,var v22:Double) {
		def setToAngle(val angle:Double)
		def setToId()
		def scale(val s:Double)
		def mul(val v:Vec2):Vec2
	}
	*/

	case class SimEnt(
		var pos:Vec2, 
		var publicId:Long, 
		var speed:Double, 
		var radius:Double, 
		var direction:Double, 
		var turnLeft:Boolean,
		var turnRight:Boolean,
		var thrust:Boolean
		) {

		def copyFromPlayer(p:Player) {
			pos      =p.pos
			publicId =p.publicId
			speed    =p.speed
			radius   =p.radius
			direction=p.direction
			turnLeft =p.turnLeft
			turnRight=p.turnRight
			thrust   =p.thrust
		}

		def copyFromShot(p:Shot) {
			pos      =p.pos
			publicId =p.publicId
			speed    =p.speed
			radius   =p.radius
			direction=p.direction
			turnLeft =false
			turnRight=false
			thrust   =true
		}
	}
		

	val worldSize=1000
	val minDistFactor=5

	override def name = myName

	var shotSpeed=10
	var shotRadius=1
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


	def processWorld(world : World) {
		val selfOpt=world.players.find(_.publicId==getPublicId)
		if (selfOpt.isEmpty) return

		val shotOpt = world.shots.find(_.parentId==getPublicId)
		val canShoot = shotOpt.isEmpty

		if (!canShoot) {
			shotSpeed=shotOpt.get.speed
			shotRadius=shotOpt.get.radius
		}

		val self      =selfOpt.get
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

		val shoot     =aim && canShoot 

		val left      =cross<0 && !shoot
		val right     =cross>0 && !shoot

		val isNear    =dist<self.radius*minDistFactor

		val ahead     = !isNear 

		lastNextPublicId=next.publicId
		lastNextPos=next.pos
		lastCanShoot=canShoot
		lastSelfPos=self.pos

		action(left,right,ahead,shoot)
	}
}
