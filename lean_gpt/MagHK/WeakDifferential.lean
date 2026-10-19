import MagHK.Poincare
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
The local weak dCoord derivative is defined by ordinary Lebesgue integrals
against smooth compactly supported test functions. The universal library below
is the standard local closed-derivative-operator calculus. Its fields are
integration by parts, linearity, locality and the C1 multiplier domain rule.
They make no assertions about magnetic eigenfunctions or reconstruction.
-/
noncomputable section
namespace MagHK.WeakDifferential
open MeasureTheory Set
open scoped ContDiff
abbrev Space := MagHK.Poincare.Space3
abbrev Index := Fin 3

def dCoord (f : Space → ℝ) (i : Index) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

structure WeakPartial (s : Set Space) (f df : Space → ℝ) (i : Index) : Prop where
  function_integrable : LocallyIntegrableOn f s
  derivative_integrable : LocallyIntegrableOn df s
  test_identity : ∀ η : Space → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
    tsupport η ⊆ s →
    (∫ x, f x * dCoord η i x) = -(∫ x, df x * η x)

/-- Standard laws of the closed local distributional derivative operators.
The multiplier rule has arbitrary C1 multipliers and arbitrary weak-domain
vectors. These are operator-domain facts, not conclusions about the examples.
-/
structure StandardWeakOperatorLibrary : Prop where
  classical : ∀ (s : Set Space), IsOpen s → ∀ f : Space → ℝ,
    ContDiffOn ℝ 1 f s → ∀ i, WeakPartial s f (dCoord f i) i
  restrict : ∀ s t : Set Space, IsOpen s → IsOpen t → t ⊆ s →
    ∀ f df i, WeakPartial s f df i → WeakPartial t f df i
  linear : ∀ s : Set Space, IsOpen s → ∀ f df g dg i,
    WeakPartial s f df i → WeakPartial s g dg i → ∀ a b : ℝ,
    WeakPartial s (fun x => a * f x + b * g x) (fun x => a * df x + b * dg x) i
  multiply : ∀ s : Set Space, IsOpen s → ∀ f g dg i,
    ContDiffOn ℝ 1 f s → WeakPartial s g dg i →
    WeakPartial s (fun x => f x * g x)
      (fun x => dCoord f i x * g x + f x * dg x) i
  congr_ae : ∀ s : Set Space, IsOpen s → ∀ f df g dg i,
    WeakPartial s f df i →
    (∀ᵐ x, x ∈ s → f x = g x) → (∀ᵐ x, x ∈ s → df x = dg x) →
    WeakPartial s g dg i
  unique : ∀ s : Set Space, IsOpen s → ∀ f df g dg i,
    WeakPartial s f df i → WeakPartial s g dg i →
    (∀ᵐ x, x ∈ s → f x = g x) → ∀ᵐ x, x ∈ s → df x = dg x

/-- Changes of notation for literal functions need no analytic premise. -/
theorem WeakPartial.congr {s : Set Space} {f df g dg : Space → ℝ} {i : Index}
    (h : WeakPartial s f df i) (hf : f = g) (hd : df = dg) :
    WeakPartial s g dg i := by simpa only [← hf, ← hd] using h

theorem StandardWeakOperatorLibrary.add (L : StandardWeakOperatorLibrary)
    {s : Set Space} (hs : IsOpen s) {f df g dg : Space → ℝ} {i : Index}
    (hf : WeakPartial s f df i) (hg : WeakPartial s g dg i) :
    WeakPartial s (fun x => f x + g x) (fun x => df x + dg x) i := by
  simpa only [one_mul] using L.linear s hs f df g dg i hf hg 1 1

theorem StandardWeakOperatorLibrary.sub (L : StandardWeakOperatorLibrary)
    {s : Set Space} (hs : IsOpen s) {f df g dg : Space → ℝ} {i : Index}
    (hf : WeakPartial s f df i) (hg : WeakPartial s g dg i) :
    WeakPartial s (fun x => f x - g x) (fun x => df x - dg x) i := by
  simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using L.linear s hs f df g dg i hf hg 1 (-1)

theorem StandardWeakOperatorLibrary.scale (L : StandardWeakOperatorLibrary)
    {s : Set Space} (hs : IsOpen s) {f df : Space → ℝ} {i : Index}
    (hf : WeakPartial s f df i) (a : ℝ) :
    WeakPartial s (fun x => a * f x) (fun x => a * df x) i := by
  simpa only [zero_mul, add_zero] using L.linear s hs f df f df i hf hf a 0

theorem partial_add (f g : Space → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Index) (x : Space) :
    dCoord (fun x => f x + g x) i x = dCoord f i x + dCoord g i x := by
  change (fderiv ℝ (f + g) x) _ = _
  rw [fderiv_add (hf x) (hg x)]
  rfl

theorem partial_sub (f g : Space → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Index) (x : Space) :
    dCoord (fun x => f x - g x) i x = dCoord f i x - dCoord g i x := by
  change (fderiv ℝ (f - g) x) _ = _
  rw [fderiv_sub (hf x) (hg x)]
  rfl

theorem partial_continuous (f : Space → ℝ) (hf : ContDiff ℝ 1 f) (i : Index) :
    Continuous (dCoord f i) :=
  (hf.continuous_fderiv (by decide)).clm_apply continuous_const


theorem dCoord_mul {x : Space} (f g : Space → ℝ) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Index) :
    dCoord (fun y => f y * g y) i x = dCoord f i x * g x + f x * dCoord g i x := by
  change (fderiv ℝ (f * g) x) (EuclideanSpace.single i 1) = _
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp [dCoord, mul_comm, add_comm]

theorem dCoord_div {x : Space} (f g : Space → ℝ) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hgz : g x ≠ 0) (i : Index) :
    dCoord (fun y => f y / g y) i x =
      (dCoord f i x * g x - f x * dCoord g i x) / g x ^ 2 := by
  have hi := (hasDerivAt_inv hgz).comp_hasFDerivAt x hg.hasFDerivAt
  have h := congrArg (fun T : Space →L[ℝ] ℝ => T (EuclideanSpace.single i 1))
    (hf.hasFDerivAt.mul hi).fderiv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul] at h
  change dCoord (fun y => f y * (g y)⁻¹) i x = _ at h
  dsimp only [dCoord] at *
  simp only [div_eq_mul_inv]
  rw [h]
  dsimp only [Function.comp_def]
  field_simp [hgz]
  <;> ring

end MagHK.WeakDifferential
