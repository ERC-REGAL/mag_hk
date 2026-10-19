import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.FinCases

/-!
The global primitive used in the one-particle argument.  The primitive is an
actual interval integral, and its derivative follows from mathlib's proved
Poincaré lemma on convex domains.  No primitive is postulated.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace MagHK.Poincare

section OneForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The straight-segment primitive based at the origin. -/
def segmentPrimitive (ω : E → E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∫ t : ℝ in 0..1, ω (t • x) x

theorem segmentPrimitive_hasFDerivAt
    (ω : E → E →L[ℝ] ℝ) (dω : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hω : ∀ x, HasFDerivAt ω (dω x) x)
    (hsymm : ∀ x u v, dω x u v = dω x v u) (x : E) :
    HasFDerivAt (segmentPrimitive ω) (ω x) x := by
  have h := Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    (convex_univ : Convex ℝ (univ : Set E))
    (ω := ω) (dω := dω)
    (fun y _ => (hω y).hasFDerivWithinAt)
    (fun y _ u _ v _ => hsymm y u v)
    (a := (0 : E)) (b := x) (mem_univ _) (mem_univ _)
  simpa only [hasFDerivWithinAt_univ, curveIntegral_segment,
    AffineMap.lineMap_apply_module', sub_zero, add_zero, segmentPrimitive] using! h

theorem segmentPrimitive_hasFDerivAt_of_symmetric
    (ω : E → E →L[ℝ] ℝ) (hω : Differentiable ℝ ω)
    (hsymm : ∀ x u v, fderiv ℝ ω x u v = fderiv ℝ ω x v u) (x : E) :
    HasFDerivAt (segmentPrimitive ω) (ω x) x :=
  segmentPrimitive_hasFDerivAt ω (fderiv ℝ ω)
    (fun y => (hω y).hasFDerivAt) hsymm x

@[simp] theorem segmentPrimitive_zero (ω : E → E →L[ℝ] ℝ) :
    segmentPrimitive ω 0 = 0 := by
  simp [segmentPrimitive]

end OneForm

section VectorField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scalar potential obtained by integrating a vector field along radial segments. -/
def vectorPotential (A : E → E) (x : E) : ℝ :=
  ∫ t : ℝ in 0..1, inner ℝ (A (t • x)) x

theorem vectorPotential_hasFDerivAt
    (A : E → E) (hA : Differentiable ℝ A)
    (hsymm : ∀ x u v, inner ℝ (fderiv ℝ A x u) v =
      inner ℝ (fderiv ℝ A x v) u) (x : E) :
    HasFDerivAt (vectorPotential A) (innerSL ℝ (A x)) x := by
  have h := segmentPrimitive_hasFDerivAt
    (fun y => innerSL ℝ (A y))
    (fun y => (innerSL ℝ).comp (fderiv ℝ A y))
    (fun y => (innerSL ℝ).hasFDerivAt.comp y (hA y).hasFDerivAt)
    (fun y u v => hsymm y u v) x
  exact h

theorem vectorPotential_hasGradientAt [CompleteSpace E]
    (A : E → E) (hA : Differentiable ℝ A)
    (hsymm : ∀ x u v, inner ℝ (fderiv ℝ A x u) v =
      inner ℝ (fderiv ℝ A x v) u) (x : E) :
    HasGradientAt (vectorPotential A) (A x) x :=
  vectorPotential_hasFDerivAt A hA hsymm x

end VectorField

section ThreeDimensions

abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- Cartesian curl, with indices `0, 1, 2` in the usual cyclic order. -/
def curl (A : Space3 → Space3) (x : Space3) : Fin 3 → ℝ :=
  ![(fderiv ℝ A x (EuclideanSpace.single 1 1)) 2 -
      (fderiv ℝ A x (EuclideanSpace.single 2 1)) 1,
    (fderiv ℝ A x (EuclideanSpace.single 2 1)) 0 -
      (fderiv ℝ A x (EuclideanSpace.single 0 1)) 2,
    (fderiv ℝ A x (EuclideanSpace.single 0 1)) 1 -
      (fderiv ℝ A x (EuclideanSpace.single 1 1)) 0]

theorem inner_symmetric_of_coordinates (D : Space3 →L[ℝ] Space3)
    (hD : ∀ i j : Fin 3, (D (EuclideanSpace.single i 1)) j =
      (D (EuclideanSpace.single j 1)) i) (u v : Space3) :
    inner ℝ (D u) v = inner ℝ (D v) u := by
  let B : LinearMap.BilinForm ℝ Space3 := (innerₛₗ ℝ).comp D.toLinearMap
  have hB : B.IsSymm :=
    (LinearMap.BilinForm.isSymm_iff_basis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis).2
      (by
        intro i j
        simpa [B, EuclideanSpace.basisFun_apply,
          EuclideanSpace.inner_single_right] using hD i j)
  exact hB.eq u v

theorem fderiv_symmetric_of_curl_eq_zero (A : Space3 → Space3)
    (hcurl : ∀ x, curl A x = 0) (x u v : Space3) :
    inner ℝ (fderiv ℝ A x u) v = inner ℝ (fderiv ℝ A x v) u := by
  have h12 : (fderiv ℝ A x (EuclideanSpace.single 1 1)) 2 =
      (fderiv ℝ A x (EuclideanSpace.single 2 1)) 1 := by
    have h := congrFun (hcurl x) 0
    simpa [curl, sub_eq_zero] using h
  have h20 : (fderiv ℝ A x (EuclideanSpace.single 2 1)) 0 =
      (fderiv ℝ A x (EuclideanSpace.single 0 1)) 2 := by
    have h := congrFun (hcurl x) 1
    simpa [curl, sub_eq_zero] using h
  have h01 : (fderiv ℝ A x (EuclideanSpace.single 0 1)) 1 =
      (fderiv ℝ A x (EuclideanSpace.single 1 1)) 0 := by
    have h := congrFun (hcurl x) 2
    simpa [curl, sub_eq_zero] using h
  apply inner_symmetric_of_coordinates
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all

/-- A globally curl-free differentiable Cartesian vector field is the gradient
of the explicit straight-segment potential. -/
theorem curl_free_hasGradientAt (A : Space3 → Space3)
    (hA : Differentiable ℝ A) (hcurl : ∀ x, curl A x = 0) (x : Space3) :
    HasGradientAt (vectorPotential A) (A x) x :=
  vectorPotential_hasGradientAt A hA (fderiv_symmetric_of_curl_eq_zero A hcurl) x

theorem curl_free_exists_potential (A : Space3 → Space3)
    (hA : ContDiff ℝ 1 A) (hcurl : ∀ x, curl A x = 0) :
    ∃ η : Space3 → ℝ, η 0 = 0 ∧ ∀ x, HasGradientAt η (A x) x := by
  refine ⟨vectorPotential A, ?_, fun x => curl_free_hasGradientAt A
    (hA.differentiable (by decide)) hcurl x⟩
  simp [vectorPotential]

end ThreeDimensions

end MagHK.Poincare
