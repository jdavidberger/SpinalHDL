package spinal.lib.formal

import spinal.core.formal.anyseq
import spinal.core.internals.{AssertStatement, AssertStatementKind}
import spinal.core.{Bool, Component, Composite, Data, MultiData, SpinalTag, SpinalWarning, True, Vec, assert, assume, cover, when}
import spinal.idslplugin.Location
import spinal.lib.IMasterSlave

import scala.collection.mutable
import scala.ref.WeakReference
import scala.util.Try

object AssertionLevel extends Enumeration {
  type Level = Value
  val None, Assertion, Assumption = Value
}

class HasFormalAssertsTag(val formalAsserts : HasFormalAsserts) extends SpinalTag


trait HasFormalAsserts { self =>
  if (!this.isInstanceOf[Component]) {
    Component.current.addTag(new HasFormalAssertsTag(this))
  }

  private val OwningComponent = WeakReference(Component.current)

  private var _CurrentAssertionLevel = AssertionLevel.None
  private def CurrentAssertionLevel = _CurrentAssertionLevel
  private def CurrentAssertionLevel_=(level: AssertionLevel.Value): Unit ={
    _CurrentAssertionLevel = level
    val kind = _CurrentAssertionLevel match {
      case AssertionLevel.Assumption => AssertStatementKind.ASSUME
      case _ => AssertStatementKind.ASSERT
    }
    runFormalChecks()
    formalProperties.foreach(_.kind = kind)
  }

  lazy private val formalValidInputsProperty = assert(formalValidInputs, s"Input into ${this} failed its assertion")

  private var _CurrentInputsAssertionLevel = AssertionLevel.None
  private def CurrentInputsAssertionLevel = _CurrentInputsAssertionLevel
  private def CurrentInputsAssertionLevel_=(level: AssertionLevel.Value): Unit ={
    assert(_CurrentInputsAssertionLevel <= level)
    _CurrentInputsAssertionLevel = level
    val kind = _CurrentInputsAssertionLevel match {
      case AssertionLevel.Assumption => AssertStatementKind.ASSUME
      case _ => AssertStatementKind.ASSERT
    }
    formalValidInputsProperty.kind = kind
  }

  def formalConfigureForTest(): this.type = {
    formalAssumeInputs()
    formalAsserts()
    this
  }

  lazy val formalValidInputs: Bool = True

  /**
   * Configure asserts around the input signals to the given object. This is kept seperate so that you can run
   * dut.formalAssertInputs()
   * dut.formalAssumes()
   *
   * which will test that the inputs to the already validated dut object adhere to whatever contract is in place for
   * it's inputs.
   */
  final def formalAssertInputs()(implicit useAssumes: Boolean = false): Unit = {
    val newLevel = if (useAssumes) AssertionLevel.Assumption else AssertionLevel.Assertion
    if(newLevel >= CurrentInputsAssertionLevel) {
      CurrentInputsAssertionLevel = newLevel
    }
  }

  final def formalAssumeInputs(): Unit = formalAssertInputs()(useAssumes = true)


  /**
   * Set o formal assertions required for testing and validating the component completely.
   *
   * @param useAssumes indicates that we want to assume all the predicates are always true; which informs inductive
   *                   provers which states are acceptable.
   * @return An area (typically a composite) which may contain signals useful for collectign during a simulation
   */
  protected def formalChecks()(implicit useAssumes: Boolean = false) : Unit = {}

  private var hasRanFormalChecks = false
  private def runFormalChecks(useAssumes : Boolean = false): Unit = {
    if(!hasRanFormalChecks) {
      hasRanFormalChecks = true

      formalValidInputsProperty
      when(formalValidInputs) {
        formalAssertsChildren(assumesInputValid = useAssumes, useAssumes = true)
        val formerCount = HasFormalAsserts.totalProperties
        formalChecks()
        propertiesBody = HasFormalAsserts.totalProperties - formerCount
      }
    }
  }

  def FormalCompositeName(implicit useAssumes: Boolean = false) = if (useAssumes) "formalAssumes" else "formalAsserts"

  private def formalAssertsChildren(assumesInputValid: Boolean, useAssumes: Boolean = false): Unit = {
    HasFormalAsserts.formalAssertsChildren(Try {
      this.asInstanceOf[Component]
    }.getOrElse(null), assumesInputValid, useAssumes)
  }

  private def formalAssertsChildren()(implicit useAssumes: Boolean): Unit = {
    formalAssertsChildren(false, useAssumes)
  }

  def formalAssertOrAssume()(implicit useAssumes: Boolean = false): Unit = {
    if (useAssumes) {
      formalAssumes()
    } else {
      formalAsserts()
    }
  }

  var propertiesBody : Int = 0

  def formalAsserts(): this.type = {
    if (CurrentAssertionLevel >= AssertionLevel.Assertion)
      return this

    formalAssertsChildren()(useAssumes = false)
    CurrentAssertionLevel = AssertionLevel.Assertion

    this
  }

  def formalAssumes(): this.type = {
    if (CurrentAssertionLevel == AssertionLevel.Assumption)
      return this

    formalAssertInputs()
    if (HasFormalAsserts.alwaysAssert) {
      formalAsserts()
    } else {
      CurrentAssertionLevel = AssertionLevel.Assumption
    }

    this
  }

  def formalProperties = new mutable.ArrayBuffer[AssertStatement]()
  /**
   * Helper function; uses the implicit useAssumes variable to either emit an assert or assume
   *
   * @param cond       Condition to assert or assume
   * @param msg        Some backends with asserts will print out a message when an assert fails. Ignored for assumes
   * @param useAssumes True to emit an assume
   */
  def assertOrAssume(cond: Bool, msg: Any*)(implicit loc: Location, useAssumes: Boolean): Unit =
    formalProperties += HasFormalAsserts.assertOrAssume(cond, msg: _*)

  def formalPropertyAdd(cond: Bool, msg: Any*)(implicit loc: Location): Unit = {
    formalProperties += (if(CurrentAssertionLevel == AssertionLevel.Assertion) assert(cond, msg) else assume(cond))
  }
}

object HasFormalAsserts {
  def printFormalAssertsReport(): Unit = {
    val allTraits = allFormalTraits()
    val allAssumed = allTraits.filter(_.CurrentAssertionLevel == AssertionLevel.Assumption)
    val allAsserted = allTraits.filter(_.CurrentAssertionLevel == AssertionLevel.Assertion)
    val allInputsAssumed = allTraits.filter(_.CurrentInputsAssertionLevel == AssertionLevel.Assumption)
    val allInputsAsserted = allTraits.filter(_.CurrentInputsAssertionLevel == AssertionLevel.Assertion)

    def formalAssertDesc(c : HasFormalAsserts): String = {
      s"Inputs: ${c.CurrentInputsAssertionLevel} Body: ${c.CurrentAssertionLevel} Properties: ${c.propertiesBody}"
    }
    def printTree(c : Component, tabs : Int = 0): Unit = {
      val desc =
        c match {
          case c: HasFormalAsserts => formalAssertDesc(c)
          case _ => ""
        }

      val prefix = "\t" * tabs
      println(s"$prefix ${c.getClass.getSimpleName} ${c.name} ${desc}")
      c.getTagsOf[HasFormalAssertsTag]().map(_.formalAsserts).foreach(c => {
        println(s"\t$prefix ${c.getClass.getSimpleName} $c ${formalAssertDesc(c)}")
      })
      c.children.foreach(printTree(_, tabs = tabs + 1))
    }

    printTree(Component.toplevel)
  }
  private def alwaysAssert: Boolean = sys.env.contains("SPINAL_FORMAL_NEVER_ASSUME")

  private def formalAssertTags(c: Component, assumesInputValid: Boolean, useAssumes: Boolean = false): Unit = {
    val direct_asserts = c.getTagsOf[HasFormalAssertsTag]().map(_.formalAsserts)

    direct_asserts.foreach(a => {
      a.formalAssertInputs()(useAssumes = assumesInputValid)
      a.formalAssertOrAssume()(useAssumes)
    })
  }

  private def allFormalTraits(c: Component = Component.toplevel): Seq[HasFormalAsserts] = {
    if (c == null) {
      return Seq()
    }

    def apply(c: Component, walkSet: mutable.HashSet[Component]): Seq[HasFormalAsserts] = {
      if (!walkSet.contains(c)) {

        walkSet += c

        (c match {
          case asserts: HasFormalAsserts => Seq(asserts)
          case _ => Seq()
        }) ++
          c.getTagsOf[HasFormalAssertsTag]().map(_.formalAsserts) ++
          c.children.flatMap(apply(_, walkSet))
      } else Seq()
    }

    val walkSet = new mutable.HashSet[Component]()
    apply(c, walkSet)
  }

  def formalAssertsChildren(c: Component, assumesInputValid: Boolean, useAssumes: Boolean = false): Unit = {
    if (c == null) {
      return
    }

    def apply(c: Component, walkSet: mutable.HashSet[Component]): Unit = {
      if (!walkSet.contains(c)) {
        formalAssertTags(c, assumesInputValid, useAssumes)

        walkSet += c
        c match {
          case c: HasFormalAsserts => {
            c.formalAssertInputs()(useAssumes = assumesInputValid)
            c.formalAssertOrAssume()(useAssumes = useAssumes)
          }
          case _ => c.walkComponents(apply(_, walkSet))
        }
      }
    }

    //c.addPrePopTask(() => {
      formalAssertTags(c, assumesInputValid, useAssumes)

      val walkSet = new mutable.HashSet[Component]()
      walkSet += c
      c.walkComponents(apply(_, walkSet))
    //})
  }

  var totalAsserts : Int = 0
  var totalAssumes : Int = 0
  def totalProperties = totalAsserts + totalAssumes

  /**
   * Helper function; uses the implicit useAssumes variable to either emit an assert or assume
   *
   * @param cond       Condition to assert or assume
   * @param msg        Some backends with asserts will print out a message when an assert fails. Ignored for assumes
   * @param useAssumes True to emit an assume
   */
  def assertOrAssume(cond: Bool, msg: Any*)(implicit loc: Location, useAssumes: Boolean): AssertStatement = {
    if (useAssumes) {
      totalAssumes += 1
      assume(cond)
    } else {
      totalAsserts += 1
      assert(cond, Seq(msg: _*))
    }
  }
}

class ComponentWithFormalAsserts extends Component with HasFormalAsserts {
  override def asFormalDut() = {
    formalConfigureForTest()
    super.asFormalDut()
  }

  private def flattenIO() : Seq[Data] = {
    def hasDirectionnSpecifier(io : Data) = io match {
      case io: IMasterSlave => (io.isSlaveInterface || io.isMasterInterface)
      case _ => !io.isDirectionLess
    }
    def recursiveWalk(io : Data): Seq[Data] = io match {
      case io: MultiData => if (hasDirectionnSpecifier(io)) Seq(io) else io.elements.map(_._2).toSeq.flatMap(recursiveWalk)
      case _ => Seq(io)
    }
    getGroupedIO(true).flatMap(recursiveWalk)
  }

  def anyseq_inputs(): Unit = {
    getAllIo.filter(_.isInput).filter(_.dlcIsEmpty).foreach(anyseq)
  }

  override lazy val formalValidInputs: Bool = {


    Vec(flattenIO().map({
      case io: FormalMasterSlave =>
        io.checkForEquivalance()

        if(io.isMasterInterface) io.formalIsConsumerValid()
        else if(io.isSlaveInterface) io.formalIsProducerValid()
        else if(io.isInput) io.formalIsValid()
        else True
      case io: FormalBundle => if(io.isInput) io.formalIsValid() else True
      case _ => True
    })).asBits.andR
  }

  protected def formalCheckOutputs()(implicit useAssumes: Boolean = false): Unit = {
    flattenIO().foreach({
      case io: FormalMasterSlave =>
        if (io.isMasterInterface) assertOrAssume(io.formalIsProducerValid())
        else assertOrAssume(io.formalIsConsumerValid())
      case io: FormalBundle => if (io.isOutput) assertOrAssume(io.formalIsValid())
      case _ => True
    })
  }

  def formalCheckOutputsAndChildren()(implicit useAssumes: Boolean = false): Unit = {
    formalCheckOutputs()
    HasFormalAsserts.formalAssertsChildren(this, assumesInputValid = false, useAssumes = true)
  }
  override protected def formalChecks()(implicit useAssumes: Boolean = false): Unit = {
    formalCheckOutputsAndChildren()
  }

  override def formalAssumes(): this.type = {
    withAutoPull()
    super.formalAssumes()
  }

  override def formalAsserts(): this.type = {
    withAutoPull()
    super.formalAsserts()
  }
}