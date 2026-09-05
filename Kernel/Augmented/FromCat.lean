import Kernel.Augmented.FromTwoCategory
import Mathlib.CategoryTheory.Category.Cat

/-! The supplied `Cat` model: vertical cells are natural transformations.
Cites: D-KR-18, D-RT-30, AT-FD-7.
This instantiates the binary cell comparison, not a discrete nerve comparison
with a completed augmented algebra or the proposed infinity-categorical root.
-/

open CategoryTheory
namespace Kernel.Augmented.FromCat
universe u v

def cellNatTransEquiv {A B : Cat.{v,u}} (F G : A ⟶ B) :
    FromTwoCategory.Cell F G ≃ (F.toFunctor ⟶ G.toFunctor) where
  toFun α := (FromTwoCategory.cellEquiv F G α).toNatTrans
  invFun η := η.toCatHom₂
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem identity {A B : Cat.{v,u}} (F : A ⟶ B) :
    cellNatTransEquiv F F (FromTwoCategory.identity F) = 𝟙 F.toFunctor := rfl

theorem alongRow {A B : Cat.{v,u}} {F G H : A ⟶ B}
    (α : FromTwoCategory.Cell F G) (β : FromTwoCategory.Cell G H) :
    cellNatTransEquiv F H (FromTwoCategory.alongRow α β) =
      cellNatTransEquiv F G α ≫ cellNatTransEquiv G H β := rfl

theorem stack {A B C : Cat.{v,u}} {F G : A ⟶ B} {H K : B ⟶ C}
    (α : FromTwoCategory.Cell F G) (β : FromTwoCategory.Cell H K) :
    cellNatTransEquiv (F ≫ H) (G ≫ K) (FromTwoCategory.stack α β) =
      Functor.whiskerRight (cellNatTransEquiv F G α) H.toFunctor ≫
        Functor.whiskerLeft G.toFunctor (cellNatTransEquiv H K β) := rfl

end Kernel.Augmented.FromCat
