package simple_trees

import javadefined.{JavaShadowingClassChild, JavaShadowingClassParent}

class JavaClassShadowing:
  def test(): Unit =
    val child: JavaShadowingClassChild = new JavaShadowingClassChild

    val parentInner = child.makeParentInnerClass()
    useParentInner(parentInner)

    // For some reason, this does not compile:
    //val otherParentInner = child.makeOtherParentInnerClass()
    //useParentInner(otherParentInner)

    val childInner = child.makeChildInnerClass()
    useChildInner(childInner)
  end test

  def useParentInner(parentInner: JavaShadowingClassParent#InnerClass): Unit =
    ()

  def useChildInner(childInner: JavaShadowingClassChild#InnerClass): Unit =
    ()
end JavaClassShadowing
