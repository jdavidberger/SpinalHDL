package spinal.lib.formal

import spinal.core._
import spinal.idslplugin.Location
import spinal.lib.IMasterSlave

trait FormalBundle {
  self =>
  type Self <: FormalBundle

  def formalIsValid() : Bool
  def formalAssertEquivalence(that : Self): Unit = {}

  def checkForEquivalance(): this.type = {
    def findTypeParent(e: Any) : Option[Self] = {
      e match {
        case self: Self =>
          Some(self)
        case b: BaseType => findTypeParent(b.parent)
        case b: MultiData => findTypeParent(b.parent)
        case _ => None
      }
    }

    def flattenElements(elements : Seq[Data]): Seq[BaseType] = {
      elements.flatMap(x => {
        x match {
          case b: BaseType =>
            if(b.isInput) Seq(b) else Seq()
          case m: MultiData => flattenElements(m.elements.map(_._2))
        }
      })
    }

    def getAssignmentBundle(e : Any): Option[Self] = {
      e match {
        case b: BaseType => {
          if(b.dlcHasOnlyOne && b.dlcHead.source.isInstanceOf[BaseType]) {
            findTypeParent(b.dlcHead.source.asInstanceOf[BaseType]).orElse(getAssignmentBundle(b.dlcHead.source))
          } else {
            None
          }
        }
        case b: MultiData => {
          val flattenedSource = flattenElements(b.elements.map(_._2))
          val assignmentSources = flattenedSource.map(x => getAssignmentBundle(x))
          val singleSource = assignmentSources.forall(assignmentSources.head == _)
          if(singleSource) {
            assignmentSources.headOption.flatten
          } else {
            None
          }
        }
        case _ => None
      }
    }

    val singleSource = getAssignmentBundle(this)
    if(singleSource.nonEmpty) {
      formalAssertEquivalence(singleSource.get)
    }

    this
  }
}

trait FormalMasterSlave extends IMasterSlave with FormalBundle {
  def formalIsProducerValid() : Bool
  def formalIsConsumerValid() : Bool = True
  override def formalIsValid() : Bool = formalIsConsumerValid() && formalIsProducerValid()
}
