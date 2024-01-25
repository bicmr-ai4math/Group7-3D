import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.IdealOperations
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Lie.Solvable
import Mathlib.LinearAlgebra.Basic
import Mathlib.Order.CompactlyGenerated
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional

open Function
open Set
open BigOperators
open Finset
variable {R : Type _} [CommRing R] {L : Type _}  [LieRing L] [LieAlgebra R L]

--define derived algebra
def derivedprimary (R : Type _) [Field R] (L : Type _)  [LieRing L] [LieAlgebra R L]
: Set L := { z : L | ∃  x y : L , z = ⁅ x , y ⁆ }
def derived (R : Type _) [Field R] (L : Type _)  [LieRing L] [LieAlgebra R L] : Submodule R L
:= Submodule.span R (derivedprimary R L)
--some theorems used later
--dimension of derived algebra is ≤ dimension of original algebra
theorem dimension_of_derived_le (R : Type _) [Field R] (L : Type _)  [LieRing L]
[LieAlgebra R L] [Module.Finite R L] : FiniteDimensional.finrank R (derived R L)
≤ FiniteDimensional.finrank R L := by
  apply Submodule.finrank_le (derived R L)
--dimension of derived algebra is finite is the original one is
theorem dimension_of_derived_finite (R : Type _) [Field R] (L : Type _)  [LieRing L]
[LieAlgebra R L] [Module.Finite R L] : Module.Finite R (derived R L) := by
  exact Module.IsNoetherian.finite R (derived R L)
--x ∈ S → x ∈ span S
theorem SinspanS {R : Type _} [Field R] {L : Type _}  [AddCommGroup L]
[Module R L] {S : Set L}(x : L) : x ∈ S →  x ∈  (Submodule.span R S).carrier := by
  intro h
  simp
  unfold Submodule.span
  apply Submodule.mem_sInf.mpr
  intro p h1
  have :  S ⊆ ↑p := by
    exact h1
  exact h1 h

theorem elementinsubmoduleisinsubmodule (R : Type _) [Field R] (L : Type _) [AddCommGroup L]
[Module R L] (S : Submodule R L) (x : L): x ∈ S → ∃ z : S , z = x := by
  intro h
  exact CanLift.prf x h
--v can be represented by a nasis in 1-dimensional case
theorem decompose (k V : Type _) [Field k] [AddCommGroup V] [Module k V] (b : Basis (Fin 1) k V) :
    ∀ (v : V), v = (b.repr v 0) • (b 0) := by
  intro v
  nth_rewrite 1 [← b.total_repr v]
  have hsubset : (b.repr v).support ⊆ {0} := by
    intro x _
    rewrite [Finset.mem_singleton]
    exact Fin.eq_zero x
  have hzero : ∀ x ∈ ({0} : Finset (Fin 1)), x ∉ (b.repr v).support → (b.repr v) x • b x = 0 := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    rw [hi, Finsupp.mem_support_iff.not, not_ne_iff]
    intro hc
    rw [hc]
    exact zero_smul k (b 0)
  rw [Finsupp.total_apply, Finsupp.sum, Finset.sum_subset hsubset hzero,
   Finset.sum_singleton]

--find a basis for a n dimensional vector space
def bov {R : Type _} [Field R] {n : ℕ } (L : Type _)  [AddCommGroup L]
[Module R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = n)
: Basis (Fin n) R L where
  repr := by sorry
--3 linear independent elements can be made into a basis if dimension of vector space is 3
theorem bov2exist (R : Type _) [Field R] (L : Type _)  [AddCommGroup L]
[Module R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = 3) (x y z : L)
(h1 : ∀ (a b c : R) , a • x + b • y + c • z = 0 → (a = 0 ∧ b = 0 ∧ c = 0)) :
∃ (B : Basis (Fin 3) R L) , (B 0 = x ∧ B 1 = y ∧ B 2 = z):= by
  let v : Fin 3 → L := ![x, y, z]
  --prove v linear independent
  have hv : LinearIndependent R v := by
    apply Fintype.linearIndependent_iff.mpr
    --intro l h2
    --simp at h2
    intro g h4
    have : g 0 • v 0 + g 1 • v 1 + g 2 • v 2 = ∑ i , g i • v i := by
      exact (Fin.sum_univ_three fun i => g i • v i).symm
    have : g 0 • v 0 + g 1 • v 1 + g 2 • v 2 = 0 := by
      rw[this]
      apply h4
    have h6: g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
      apply h1 (g 0) (g 1) (g 2) this
    intro i
    have : i.val <3 := by
      exact Fin.prop i
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
      have : i.val ≤ 2 := by
        apply Nat.le_pred_of_lt this
      rcases em (i.val = 2) with q | q
      · tauto
      · have : i.val < 2 := by
          contrapose! q
          apply le_antisymm this q
        have : i.val ≤ 1 := by
          apply Nat.le_pred_of_lt this
        rcases em (i.val = 1) with r | r
        · tauto
        · have : i.val < 1 := by
            contrapose! r
            apply le_antisymm this r
          have : i.val ≤ 0 := by
            apply Nat.le_pred_of_lt this
          have : i.val = 0 := by
            apply le_antisymm this (Nat.zero_le i.val)
          tauto
    rcases this with p0 | p1| p2
    · have : i = 0 := by
        exact Fin.ext p0
      rw[this]
      tauto
    · have : i = 1 := by
        exact Fin.ext p1
      rw[this]
      tauto
    · have : i = 2 := by
        exact Fin.ext p2
      rw[this]
      tauto
  --apply basisOfLinearIndependentOfCardEqFinrank to v
  let B : Basis (Fin 3) R L := basisOfLinearIndependentOfCardEqFinrank hv (by rw [h]; rfl)
  use B
  simp

--choose a basis
noncomputable def bov2 (R : Type _) [Field R] (L : Type _)  [AddCommGroup L]
[Module R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = 3) (x y z : L)
(h1 : ∀ (a b c : R) , a • x + b • y + c • z = 0 → (a = 0 ∧ b = 0 ∧ c = 0)) : Basis (Fin 3) R L :=
  Classical.choose (bov2exist R L h x y z h1)

--choose z s.t. x y z linear independent given x y linear independent
theorem bov3exist (R : Type _) [Field R] (L : Type _)  [AddCommGroup L]
[Module R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = 3) (x y : L)
(h1 : ∀ (a b : R) , a • x + b • y  = 0 → (a = 0 ∧ b = 0)) : ∃ (z : L) ,
∀ (a b c : R) , a • x + b • y + c • z = 0 → (a = 0 ∧ b = 0 ∧ c = 0) := by
  sorry
--choose a basis given x y linear independent
noncomputable def bov3 (R : Type _) [Field R] (L : Type _)  [AddCommGroup L]
[Module R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = 3) (x y: L)
(h1 : ∀ (a b: R) , a • x + b • y = 0 → (a = 0 ∧ b = 0)) : Basis (Fin 3) R L :=
  Classical.choose (bov2exist R L h x y (Classical.choose (bov3exist R L h x y h1)) (Classical.choose_spec (bov3exist R L h x y h1)) )


theorem natle3is0123 {n : ℕ }(h : n ≤ 3) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
  rcases em (n = 3) with p | p
  · tauto
  · have : n < 3 := by
      contrapose! p
      apply le_antisymm h p
    have : n ≤ 2 := by
      apply Nat.le_pred_of_lt this
    rcases em (n = 2) with q | q
    · tauto
    · have : n < 2 := by
        contrapose! q
        apply le_antisymm this q
      have : n ≤ 1 := by
        apply Nat.le_pred_of_lt this
      rcases em (n = 1) with r | r
      · tauto
      · have : n < 1 := by
          contrapose! r
          apply le_antisymm this r
        have : n ≤ 0 := by
          apply Nat.le_pred_of_lt this
        have : n = 0 := by
          apply le_antisymm this (Nat.zero_le n)
        tauto
--dimension of derived algebra is 0,1,2,or3
theorem dimension_of_derived_is_0123 (R : Type _) [Field R] (L : Type _)  [LieRing L]
[LieAlgebra R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = 3):
FiniteDimensional.finrank R (derived R L) = 0 ∨ FiniteDimensional.finrank R (derived R L) =1 ∨
FiniteDimensional.finrank R (derived R L) = 2 ∨ FiniteDimensional.finrank R (derived R L) = 3 := by
  have : FiniteDimensional.finrank R (derived R L) ≤ 3 := by
    rw[← h]
    apply dimension_of_derived_le R L
  apply natle3is0123 this

--derived algebra has dimension 0
--a vector in 0-dimensional space is 0
theorem zerodimensionalvectorspaceis0 {R : Type _} [Field R] {L : Type _}  [AddCommGroup L][Module R L] [Module.Finite R L]
(h : FiniteDimensional.finrank R L = 0) (x : L) : x = 0 := by
  have : ((bov L h).repr.toFun x).toFun= ((bov L h).repr.toFun 0).toFun := by
    exact List.ofFn_inj.mp rfl
  have h3: (bov L h).repr.toFun x = (bov L h).repr.toFun 0 := by
    exact Finsupp.ext (congrFun this)
  have : (bov L h).repr.invFun ((bov L h).repr.toFun x) = x := by
    exact (bov L h).repr.left_inv x
  rw[← this]
  have : (bov L h).repr.invFun ((bov L h).repr.toFun 0) = 0 := by
    exact (bov L h).repr.left_inv 0
  rw[← this]
  exact congrArg (bov L h).repr.invFun h3

theorem elementin0dimensionderivedis0 {R : Type _} [Field R] {L : Type _}
[LieRing L][LieAlgebra R L] [Module.Finite R L]
(h1 : FiniteDimensional.finrank R (derived R L) = 0) (x : L) : x ∈ (derived R L) → x = 0 := by
  intro h
  have : ∃ z : (derived R L) , z = x := by
    apply elementinsubmoduleisinsubmodule R L (derived R L) x h
  rcases this with ⟨ z , hz ⟩
  have : z = 0 := by
    apply zerodimensionalvectorspaceis0 h1 z
  rw[← hz]
  apply Submodule.coe_eq_zero.mpr this
--[x , y] is in derived algebra
theorem branketinderived {R : Type _} [Field R] {L : Type _}[LieRing L][LieAlgebra R L]
[Module.Finite R L] (x y : L) : ⁅ x , y⁆ ∈ derived R L := by
  have : ⁅ x , y ⁆ ∈ derivedprimary R L := by

    let z := ⁅ x , y ⁆
    have : z =⁅ x , y ⁆ := by
      tauto
    have : z ∈ derivedprimary R L := by
      apply Set.mem_setOf.mpr
      use x
      use y

    tauto
  apply SinspanS ⁅ x , y ⁆ this



--if dimension of derived algebra is 0, then Lie algebra is trivial
theorem dim0derivediscommutative {R : Type _} [Field R] {L : Type _}
[LieRing L][LieAlgebra R L] [Module.Finite R L](h1 : FiniteDimensional.finrank R (derived R L) = 0)
(x y : L) : ⁅ x , y⁆ = 0 := by
  have : ⁅ x , y ⁆ ∈ derived R L := by
    apply branketinderived x y
  apply elementin0dimensionderivedis0 h1 ⁅ x , y ⁆ this
--dimension of derived algebra is 1
theorem axeq0xneq0 {R : Type _} [Field R] {L : Type _}[LieRing L][LieAlgebra R L] [Module.Finite R L] (a : R)
(x : L) (h : a • x = 0 ) (h1 :x ≠ 0) : a = 0 := by
  have : a = 0 ∨ x = 0 := by
    exact smul_eq_zero.mp h
  rcases this with p | q
  · tauto
  · apply absurd q h1
-- if derived algebra is in center, choose x,y s.t. [x,y]≠0, then x,y,[x,y] linear independent
theorem dcxybl {R : Type _} [Field R] {L : Type _}
[LieRing L][LieAlgebra R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = 3)(x y : L)
(h1 : ⁅x , y⁆  ≠  0 ) (h2 : ∀ (w z : L) , w ∈ (derived R L) → ⁅w , z⁆  = 0) :
 ∀ (a b c : R) , a • x + b • y + c • ⁅x , y⁆= 0 → (a = 0∧ b = 0 ∧ c = 0) := by
  intro a b c h3
  have h4: ⁅ a • x + b • y + c • ⁅x , y⁆ , x⁆ = 0 := by
    rw[h3]
    simp
  have h5: ⁅ x , y ⁆ ∈ derived R L := by
    apply branketinderived x y
  have h7: (0 : L) = b • ⁅ y , x⁆ := by
    calc
      0 = ⁅ a • x + b • y + c • ⁅x , y⁆ , x⁆ := by
        symm
        apply h4
      _ = b •  ⁅ y , x⁆ + c • ⁅ ⁅x , y⁆ , x⁆ := by
        simp
      _ = b •  ⁅ y , x⁆ + c • 0:= by
        rw[h2 ⁅x , y⁆ x h5]
      _ = b •  ⁅ y , x⁆ := by
        simp
  have :  ⁅ y , x⁆ ≠  0 := by
    intro q
    have : ⁅ x , y⁆ = 0 := by
        have : (0 : L) = - (0 : L) := by
          simp
        rw[this]
        rw[← q]
        simp
    apply absurd this h1
  have bis0: b = 0 := by
    apply axeq0xneq0 b ⁅ y , x⁆ h7.symm this
  have ais0: a = 0 := by sorry
  have : 0 = c • ⁅x , y⁆ := by
    rw[← h3]
    rw[bis0 , ais0]
    simp
  have : c = 0 := by
    apply axeq0xneq0 c ⁅x , y⁆ this.symm h1
  tauto
--structure of case: erived algebra is in center and has dimension 1
theorem dim_of_derived_1_derived_in_center {R : Type _} [Field R] {L : Type _}
[LieRing L][LieAlgebra R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = 3)
(h1 : FiniteDimensional.finrank R (derived R L) =1 ) (h2 : ∀ (w z : L) , w ∈ (derived R L) → ⁅w , z⁆  = 0) :
∃ (B : Basis (Fin 3) R L) , ⁅B 0, B 1⁆ = B 2 ∧ ⁅ B 0 , B 2 ⁆ = 0 ∧  ⁅ B 1 , B 2 ⁆ = 0 := by
  have h1': ∃ (x y : L) , ⁅x , y⁆ ≠ 0 := by sorry
  rcases h1' with ⟨ x , y , h1xy⟩
  use bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2)
  --let B := bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2)
  --have Bis: B = bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2) := by rfl
  have : (bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2)) 0 = x ∧ (bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2)) 1 = y ∧ (bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2)) 2 = ⁅x , y⁆ := by
    apply Classical.choose_spec (bov2exist R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2))
  have : (bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2)) 0 = x := by tauto
  rw[this]
  have : (bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2)) 1 = y := by tauto
  rw[this]
  have : (bov2 R L h x y ⁅x , y⁆ (dcxybl h x y h1xy h2)) 2 = ⁅x , y⁆ := by tauto
  rw[this]
  have : ⁅ x , y ⁆ ∈ derivedprimary R L := by

    let z := ⁅ x , y ⁆
    have : z =⁅ x , y ⁆ := by
      tauto
    have : z ∈ derivedprimary R L := by
      apply Set.mem_setOf.mpr
      use x
      use y

    tauto
  have h5: ⁅ x , y ⁆ ∈ derived R L := by
    apply SinspanS ⁅ x , y ⁆ this
  constructor
  · rfl
  constructor
  · calc
    ⁅x , ⁅x , y⁆ ⁆ = -⁅ ⁅x , y⁆ , x ⁆ := by
      sorry
    _ = -0 := by
      rw[h2 ⁅x , y⁆ x h5]
    _ = 0 := by
      simp
  calc
  ⁅y , ⁅x , y⁆ ⁆ = -⁅ ⁅x , y⁆ , y ⁆ := by
     sorry
  _ = -0 := by
    rw[h2 ⁅x , y⁆ y h5]
  _ = 0 := by
    simp
--derived algebra has dimension 1, any nonzero element w in derived algebra can represent [s,t]
theorem repr1 {R : Type _} [Field R] {L : Type _}
[LieRing L][LieAlgebra R L] [Module.Finite R L] (h1 : FiniteDimensional.finrank R (derived R L) =1 )
 (w : L) (h2 : w ∈ (derivedprimary R L))(h3 : w ≠ 0) :
∀ (s t : L) ,  ∃ (a : R) , ⁅ s , t ⁆ = a • w := by
  intro s t
  have : w ∈ (derived R L) := by
    apply (SinspanS w h2)
  let w' : (derived R L) := Classical.choose (elementinsubmoduleisinsubmodule R L (derived R L) w this)
  have w'isw: w' = w := by
    apply Classical.choose_spec (elementinsubmoduleisinsubmodule R L (derived R L) w this)
  have reprw': w' = ((bov (derived R L) h1).repr (w') 0) • (bov (derived R L) h1) 0 := by
    apply (decompose R (derived R L) (bov (derived R L) h1) w')
  let wz : (derived R L) := Classical.choose (elementinsubmoduleisinsubmodule R L (derived R L) ⁅ s , t⁆ (branketinderived s t))
  have wziswz: wz = ⁅ s , t⁆ := by
    apply Classical.choose_spec (elementinsubmoduleisinsubmodule R L (derived R L) ⁅ s , t⁆ (branketinderived s t))
  have reprwz: wz = ((bov (derived R L) h1).repr (wz) 0) • (bov (derived R L) h1) 0 := by
    apply (decompose R (derived R L) (bov (derived R L) h1) wz)
  have reprw'neq0: ((bov (derived R L) h1).repr (w') 0) ≠ 0 := by
    intro p
    have : w = 0 := by
      rw[← w'isw, reprw',p]
      simp
    apply absurd this h3
  use ((bov (derived R L) h1).repr (wz) 0) /  ((bov (derived R L) h1).repr (w') 0)

  nth_rewrite 1 [← w'isw ]
  rw[ ← wziswz]
  nth_rewrite 1 [reprwz]
  nth_rewrite 2 [reprw']
  let b' := (bov (derived R L) h1).repr (wz) 0
  have : b' = (bov (derived R L) h1).repr (wz) 0 := by rfl
  rw[← this]
  let c' := (bov (derived R L) h1).repr (w') 0
  have : c' = (bov (derived R L) h1).repr (w') 0 := by rfl
  rw[← this]
  have : ↑ (c' • (bov ((derived R L)) h1) 0) = c' • ↑ ((bov ((derived R L)) h1) 0) := by rfl
  rw[this]
  have : ↑(b' • (bov (↥(derived R L)) h1) 0) = (b' / c') • ↑(c' • (bov (↥(derived R L)) h1) 0) := by
    calc
    ↑(b' • (bov (↥(derived R L)) h1) 0) = ((b' / c') * c') • (bov ((derived R L)) h1) 0 := by
      rw[div_mul_cancel b' reprw'neq0]
    _ = (b' / c') • ↑(c' • (bov (↥(derived R L)) h1) 0) := by
      apply mul_smul (b' / c') c' ((bov ((derived R L)) h1) 0)
  rw[this]
  tauto
--structure in case : derived algebra has dimension 1 and is not contained in center(incomplete,we can choose a to be 1)
theorem dimensionofderivedis1derivednotincenter {R : Type _} [Field R] {L : Type _}
[LieRing L][LieAlgebra R L] [Module.Finite R L] (h : FiniteDimensional.finrank R L = 3)
(h1 : FiniteDimensional.finrank R (derived R L) =1 ) (h2 : ∃  (w z: L) , w ∈ (derivedprimary R L) ∧  ⁅w , z⁆ ≠  0) :
∃ (B : Basis (Fin 3) R L)(a : R) , a ≠ 0 ∧ ⁅B 0, B 1⁆ = a • B 0  ∧ ⁅ B 0 , B 2 ⁆ = 0 ∧  ⁅ B 1 , B 2 ⁆ = 0 := by
  rcases h2 with ⟨ w, z , ⟨ hw , hwz⟩ ⟩
  have wneq0: w ≠ 0 := by sorry
  let a' := Classical.choose (repr1 h1 w hw wneq0 w z)
  have h6:  ⁅ w , z ⁆ = a' • w := by
    apply Classical.choose_spec (repr1 h1 w hw wneq0 w z)
  have h5 : a' ≠ 0 := by
    intro p
    have : ⁅ w , z ⁆ = 0 := by
      rw[h6 , p]
      simp
    apply absurd this hwz
  have h4: ∀ (a b : R) , a • w + b • z = 0 → (a = 0 ∧ b = 0):= by
    intro a b h
    have h7: a • ⁅ w , z ⁆ = 0 := by
      calc
      a • ⁅ w , z ⁆ = ⁅ a • w + b • z , z⁆ := by
        simp
      _ = 0 := by
        rw[h]
        simp
    have ais0: a = 0 := by
      apply axeq0xneq0 a ⁅w , z⁆ h7 hwz
    have bis0 : b = 0 := by
      sorry
    tauto
  --choose v s.t. w,z,v linear independent
  let v : L := Classical.choose (bov3exist R L h w z h4)
  have h8 : ∀ (a b c : R) , a • w + b • z + c • v = 0 → (a = 0 ∧ b = 0 ∧ c = 0) := by
    exact Classical.choose_spec (bov3exist R L h w z h4)
  have wneq0: w ≠ 0 := by
    intro p
    have : ⁅ w , z ⁆ = 0 := by
      rw[p]
      simp
    apply absurd this hwz
  let s := Classical.choose (repr1 h1 w hw wneq0 v w)
  have vwsw: ⁅ v , w⁆ = s • w := by
    apply Classical.choose_spec (repr1 h1 w hw wneq0 v w)
  let t := Classical.choose (repr1 h1 w hw wneq0 v z)
  have vztw: ⁅ v , z⁆ = t • w := by
    apply Classical.choose_spec (repr1 h1 w hw wneq0 v z)
  let v' := v - (t / a') • w + (s / a') • z
  --change v to v' s.t.w z v' satisfies the conditions
  have reprv': v' = v - (t / a') • w + (s / a') • z := by rfl
  have h9 : ∀ (a b c : R) , a • w + b • z + c • v' = 0 → (a = 0 ∧ b = 0 ∧ c = 0) := by
    intro a b c h13
    have : 0 = (a - (c * (t / a'))) • w + (b + (c * (s / a'))) • z + c • v:= by
      calc
      0 = a • w + b • z + c • v' := by
        apply h13.symm
      _ = a • w + b • z + c • (v - (t / a') • w + (s / a') • z) := by
        rw[reprv']
      _ = a • w + b • z + c • (v + (- (t / a')) • w + (s / a') • z) := by
        sorry
      _ = a • w + b • z + c • v + c • (-(t / a')) • w + c • (s / a') • z := by
        sorry
      _ = (a - (c * (t / a'))) • w + (b + (c * (s / a'))) • z + c • v := by
        sorry
    have : (a - (c * (t / a'))) = 0 ∧ (b + (c * (s / a'))) = 0 ∧ c = 0 := by
      apply h8 (a - (c * (t / a'))) (b + (c * (s / a'))) c this.symm
    rcases this with ⟨ h15 , h16 , h17⟩
    have : a = 0 := by
      rw[← h15 , h17]
      simp
    have : b = 0 := by
      rw[← h16 , h17]
      simp
    tauto
  use (bov2 R L h w z v' h9)
  use a'
  have : (bov2 R L h w z v' h9) 0 = w ∧ (bov2 R L h w z v' h9) 1 = z ∧ (bov2 R L h w z v' h9) 2 = v' := by
    apply Classical.choose_spec (bov2exist R L h w z v' h9)
  rcases this with ⟨ h18 , h19, h20⟩
  rw[h18 , h19 , h20]
  constructor
  · exact h5
  constructor
  · exact h6
  constructor
  · calc
    ⁅w, v'⁆ = ⁅w, v - (t / a') • w + (s / a') • z⁆ := by
      rw[← reprv']
    _ = ⁅w , v⁆ -⁅ w , (t / a') • w⁆ + ⁅ w , (s / a') • z⁆ := by
      simp
    _ = ⁅w , v⁆ - (t / a') •  ⁅w , w⁆ + (s / a') • ⁅w , z⁆ := by
      simp
    _ =- ⁅v , w⁆  + (s / a') • ⁅w , z⁆ := by
      simp
    _ = - (s • w) + (s / a') • a' • w := by
      rw[vwsw,h6]
    _ = - (s • w) + ((s / a') * a') • w := by
      rw[mul_smul]
    _ = - (s • w) + s • w := by
      rw[div_mul_cancel s h5]
    _ = 0 := by
      simp
  · sorry
