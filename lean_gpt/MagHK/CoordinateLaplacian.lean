import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-! General second-derivative chain rule and coordinate contraction for
literal Cartesian Laplacians. No external background premise is introduced. -/
noncomputable section
namespace MagHK.CoordinateLaplacian
open Filter
open scoped ContDiff Topology BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The second derivative along an actual C2 curve. -/
theorem second_curve_derivative (f : X → ℂ) (γ : ℝ → X) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (γ t)) (hγ : ContDiffAt ℝ 2 γ t) :
    deriv (deriv (f ∘ γ)) t =
      fderiv ℝ (fderiv ℝ f) (γ t) (deriv γ t) (deriv γ t) +
        fderiv ℝ f (γ t) (deriv (deriv γ) t) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (γ t) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hγd : DifferentiableAt ℝ (deriv γ) t :=
    (hγ.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hγ₁ := hγ.differentiableAt (by norm_num)
  have hd := (hfd.hasFDerivAt.comp_hasDerivAt t hγ₁.hasDerivAt).clm_apply hγd.hasDerivAt
  have he : deriv (f ∘ γ) =ᶠ[𝓝 t] fun s => fderiv ℝ f (γ s) (deriv γ s) := by
    filter_upwards [hγ.continuousAt.eventually (hf.eventually (by norm_num)),
      hγ.eventually (by norm_num)] with s hfs hγs
    exact fderiv_comp_deriv s (hfs.differentiableAt (by norm_num))
      (hγs.differentiableAt (by norm_num))
  exact he.deriv_eq.trans hd.deriv

/-- The first derivative along a curve, recorded in the same notation. -/
theorem first_curve_derivative (f : X → ℂ) (γ : ℝ → X) (t : ℝ)
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : DifferentiableAt ℝ γ t) :
    deriv (f ∘ γ) t = fderiv ℝ f (γ t) (deriv γ t) :=
  fderiv_comp_deriv t hf hγ

/-- Hessian trace in a specified Cartesian basis. -/
def laplacian (basis : Fin 3 → X) (f : X → ℂ) (x : X) : ℂ :=
  ∑ j : Fin 3, fderiv ℝ (fderiv ℝ f) x (basis j) (basis j)

/-- A coordinate Laplacian follows from the second chain rule, the inverse
metric contraction and cancellation of the coordinate acceleration/drift. -/
theorem laplacian_from_curves (basis : Fin 3 → X) (f : X → ℂ) (x : X)
    (γ : Fin 3 → ℝ → X) (t w b : Fin 3 → ℝ)
    (hx : ∀ i, γ i (t i) = x)
    (hf : ContDiffAt ℝ 2 f x)
    (hγ : ∀ i, ContDiffAt ℝ 2 (γ i) (t i))
    (hmetric : ∀ B : X →L[ℝ] X →L[ℝ] ℂ,
      (∑ i : Fin 3, w i • B (deriv (γ i) (t i)) (deriv (γ i) (t i))) =
        ∑ j : Fin 3, B (basis j) (basis j))
    (hdrift : (∑ i : Fin 3, (w i • deriv (deriv (γ i)) (t i) +
      b i • deriv (γ i) (t i))) = 0) :
    laplacian basis f x =
      ∑ i : Fin 3, (w i • deriv (deriv (f ∘ γ i)) (t i) +
        b i • deriv (f ∘ γ i) (t i)) := by
  have hsecond (i : Fin 3) := second_curve_derivative f (γ i) (t i)
    (by simpa only [hx i] using hf) (hγ i)
  have hfirst (i : Fin 3) := first_curve_derivative f (γ i) (t i)
    (by simpa only [hx i] using hf.differentiableAt (by norm_num))
    ((hγ i).differentiableAt (by norm_num))
  simp only [hx] at hsecond hfirst
  simp_rw [hsecond, hfirst, smul_add, add_assoc]
  rw [Finset.sum_add_distrib, hmetric]
  have hzero : (∑ i : Fin 3,
      (w i • fderiv ℝ f x (deriv (deriv (γ i)) (t i)) +
        b i • fderiv ℝ f x (deriv (γ i) (t i)))) = 0 := by
    have h := congrArg (fderiv ℝ f x) hdrift
    simpa only [map_sum, map_add, map_smul, map_zero] using h
  rw [hzero, add_zero]
  rfl

/-- Component inverse-metric identities imply contraction of every actual
continuous bilinear map. The basis decomposition is an algebraic identity. -/
theorem bilinear_contraction (basis : Fin 3 → X) (component : X → Fin 3 → ℝ)
    (decompose : ∀ x, x = ∑ j : Fin 3, component x j • basis j)
    (v : Fin 3 → X) (w : Fin 3 → ℝ)
    (metric : ∀ j k, (∑ i : Fin 3, w i * component (v i) j * component (v i) k) =
      if j = k then 1 else 0) (B : X →L[ℝ] X →L[ℝ] ℂ) :
    (∑ i : Fin 3, w i • B (v i) (v i)) = ∑ j : Fin 3, B (basis j) (basis j) := by
  have expand (u : X) : B u u =
      ∑ j : Fin 3, ∑ k : Fin 3,
        (component u j * component u k) • B (basis j) (basis k) := by
    calc
      B u u = B (∑ j : Fin 3, component u j • basis j)
          (∑ k : Fin 3, component u k • basis k) := by
        conv_lhs => rw [decompose u]
      _ = _ := by
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_comm]
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (w i * component (v i) j * component (v i) k) • B (basis j) (basis k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [expand]
      simp only [Finset.smul_sum, smul_smul, mul_assoc]
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
        (w i * component (v i) j * component (v i) k) • B (basis j) (basis k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [← Finset.sum_smul, metric]
      simp

end MagHK.CoordinateLaplacian
