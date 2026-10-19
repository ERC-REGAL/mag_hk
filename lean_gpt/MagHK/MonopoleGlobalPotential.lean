import MagHK.MonopoleFlux
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A direct closed-sphere Stokes obstruction. The sphere is parametrized by
colatitude and azimuth on a rectangle. Mathlib's proved rectangle divergence
theorem cancels its periodic edges and the collapsed polar edges. No Stokes
or no-monopole-potential assertion is added as an external premise. -/
noncomputable section
namespace MagHK.MonopoleGlobalPotential
open MeasureTheory Set Filter
open MagHK.MonopoleGeometry MagHK.MonopoleQuadrature
open scoped ContDiff Topology
set_option maxHeartbeats 1200000

abbrev Space := MagHK.MonopoleQuadrature.Space
abbrev Angle := ℝ × ℝ

/-- Cross product in the positively oriented coordinates (z,x,y). -/
def cross (u v : Space) : Space := WithLp.toLp 2
  ((WithLp.ofLp u).2.re * (WithLp.ofLp v).2.im -
    (WithLp.ofLp u).2.im * (WithLp.ofLp v).2.re,
   Complex.mk ((WithLp.ofLp u).2.im * (WithLp.ofLp v).1 -
      (WithLp.ofLp u).1 * (WithLp.ofLp v).2.im)
    ((WithLp.ofLp u).1 * (WithLp.ofLp v).2.re -
      (WithLp.ofLp u).2.re * (WithLp.ofLp v).1))

/-- Literal differential formulation of curl A = B. The two-form d(A·dx)
is evaluated on arbitrary real tangent vectors. -/
def HasCurl (A B : Space → Space) : Prop := ∀ x : Space, x ≠ 0 →
  ∀ u v : Space, inner ℝ (fderiv ℝ A x u) v - inner ℝ (fderiv ℝ A x v) u =
    inner ℝ (B x) (cross u v)

def sphere (p : Angle) : Space := WithLp.toLp 2
  (Real.cos p.1, (Real.sin p.1 : ℂ) * circle p.2)
def thetaTangent (p : Angle) : Space := WithLp.toLp 2
  (-Real.sin p.1, (Real.cos p.1 : ℂ) * circle p.2)
def phiTangent (p : Angle) : Space := WithLp.toLp 2
  (0, (Real.sin p.1 : ℂ) * (Complex.I * circle p.2))

private theorem circle_derivative (φ : ℝ) :
    HasDerivAt circle (Complex.I * circle φ) φ := by
  have h := (Real.hasDerivAt_cos φ).ofReal_comp.add
    ((Real.hasDerivAt_sin φ).ofReal_comp.mul_const Complex.I)
  change HasDerivAt circle ((-Real.sin φ : ℝ) + (Real.cos φ : ℂ) * Complex.I) φ at h
  have he : ((-Real.sin φ : ℝ) : ℂ) + (Real.cos φ : ℂ) * Complex.I =
      Complex.I * circle φ := by
    apply Complex.ext <;> simp only [circle, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    <;> ring
  rwa [he] at h

theorem sphere_smooth : ContDiff ℝ ∞ sphere := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℂ).symm.contDiff.comp
  apply ContDiff.prodMk contDiff_fst.cos
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst.sin).mul
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd.cos).add
      ((Complex.ofRealCLM.contDiff.comp contDiff_snd.sin).mul contDiff_const))

theorem sphere_norm (p : Angle) : ‖sphere p‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖Real.cos p.1‖ ^ 2 + ‖(Real.sin p.1 : ℂ) * circle p.2‖ ^ 2 = 1 ^ 2
  simp only [norm_mul, circle_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq p.1]

theorem sphere_ne_zero (p : Angle) : sphere p ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [sphere_norm]; norm_num)

theorem sphere_theta (p : Angle) : fderiv ℝ sphere p (1, 0) = thetaTangent p := by
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℂ).symm.hasFDerivAt.comp_hasDerivAt p.1
    ((Real.hasDerivAt_cos p.1).prodMk
      ((Real.hasDerivAt_sin p.1).ofReal_comp.mul_const (circle p.2)))
  have h' := (sphere_smooth.differentiable (by norm_num) p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  change HasDerivAt (fun t => sphere (t, p.2)) (thetaTangent p) p.1 at h
  change HasDerivAt (fun t => sphere (t, p.2)) (fderiv ℝ sphere p (1, 0)) p.1 at h'
  exact h'.unique h

theorem sphere_phi (p : Angle) : fderiv ℝ sphere p (0, 1) = phiTangent p := by
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℂ).symm.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 (Real.cos p.1)).prodMk
      ((circle_derivative p.2).const_mul (Real.sin p.1 : ℂ)))
  have h' := (sphere_smooth.differentiable (by norm_num) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  change HasDerivAt (fun t => sphere (p.1, t)) (phiTangent p) p.2 at h
  change HasDerivAt (fun t => sphere (p.1, t)) (fderiv ℝ sphere p (0, 1)) p.2 at h'
  exact h'.unique h

theorem tangent_cross (p : Angle) :
    cross (thetaTangent p) (phiTangent p) = Real.sin p.1 • sphere p := by
  have hc : (circle p.2).re ^ 2 + (circle p.2).im ^ 2 = 1 := by
    have hn : Complex.normSq (circle p.2) = 1 := by
      rw [Complex.normSq_eq_norm_sq, circle_norm]
      norm_num
    simpa only [Complex.normSq_apply, pow_two] using hn
  apply WithLp.ofLp_injective
  ext
  · simp only [cross, thetaTangent, phiTangent, sphere, WithLp.ofLp_toLp,
      WithLp.ofLp_smul, Prod.smul_fst, smul_eq_mul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, mul_zero, sub_zero, zero_sub, add_zero, zero_add]
    nlinarith only [congrArg (fun a : ℝ => Real.sin p.1 * Real.cos p.1 * a) hc]
  · simp only [cross, thetaTangent, phiTangent, sphere, WithLp.ofLp_toLp,
      WithLp.ofLp_smul, Prod.smul_snd]
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    <;> ring

/-- Components of the pullback of A·dx to the smooth sphere parametrization. -/
def pullback (A : Space → Space) (e : Angle) (p : Angle) : ℝ :=
  inner ℝ (A (sphere p)) (fderiv ℝ sphere p e)

private theorem composed_smooth (A : Space → Space)
    (hA : ContDiffOn ℝ 1 A ({0}ᶜ : Set Space)) :
    ContDiff ℝ 1 (fun p => A (sphere p)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  exact ((hA _ (sphere_ne_zero p)).contDiffAt
    (isOpen_compl_singleton.mem_nhds (sphere_ne_zero p))).comp p
      (sphere_smooth.of_le (by norm_num)).contDiffAt

private theorem pullback_smooth (A : Space → Space)
    (hA : ContDiffOn ℝ 1 A ({0}ᶜ : Set Space)) (e : Angle) :
    ContDiff ℝ 1 (pullback A e) :=
  (composed_smooth A hA).inner ℝ
    ((sphere_smooth.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)

/-- The chain rule and symmetry of the sphere's actual Hessian. -/
theorem pullback_curvature (A : Space → Space)
    (hA : ContDiffOn ℝ 1 A ({0}ᶜ : Set Space)) (p : Angle) :
    fderiv ℝ (pullback A (0, 1)) p (1, 0) -
      fderiv ℝ (pullback A (1, 0)) p (0, 1) =
    inner ℝ (fderiv ℝ A (sphere p) (thetaTangent p)) (phiTangent p) -
      inner ℝ (fderiv ℝ A (sphere p) (phiTangent p)) (thetaTangent p) := by
  have hcomp := (composed_smooth A hA).differentiable (by norm_num) p
  have hsd := (sphere_smooth.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) p
  have hdiffA := ((hA _ (sphere_ne_zero p)).contDiffAt
    (isOpen_compl_singleton.mem_nhds (sphere_ne_zero p))).differentiableAt (by norm_num)
  have hdiffS := sphere_smooth.differentiable (by norm_num) p
  have hsym := (sphere_smooth.contDiffAt (x := p)).isSymmSndFDerivAt (by norm_num) (1, 0) (0, 1)
  unfold pullback
  rw [fderiv_inner_apply ℝ hcomp (hsd.clm_apply (differentiableAt_const _)),
    fderiv_inner_apply ℝ hcomp (hsd.clm_apply (differentiableAt_const _))]
  rw [fderiv_clm_apply hsd (differentiableAt_const _),
    fderiv_clm_apply hsd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [show (fun y => A (sphere y)) = A ∘ sphere from rfl,
    fderiv_comp p hdiffA hdiffS]
  simp only [ContinuousLinearMap.comp_apply, sphere_theta, sphere_phi]
  rw [hsym]
  ring

/-- The surface integral of d(A·dx) vanishes, proved from the rectangle
fundamental theorem. The parametrization stays on the unit sphere, so A
needs no extension through the missing origin. -/
theorem closed_sphere_integral (A : Space → Space)
    (hA : ContDiffOn ℝ 1 A ({0}ᶜ : Set Space)) :
    (∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (-Real.pi)..Real.pi,
      fderiv ℝ (pullback A (0, 1)) (θ, φ) (1, 0) -
        fderiv ℝ (pullback A (1, 0)) (θ, φ) (0, 1)) = 0 := by
  let P := pullback A (0, 1)
  let Q := fun p => -pullback A (1, 0) p
  have hP : ContDiff ℝ 1 P := pullback_smooth A hA _
  have hQ : ContDiff ℝ 1 Q := (pullback_smooth A hA _).neg
  have hint : IntegrableOn (fun p => fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1))
      (uIcc 0 Real.pi ×ˢ uIcc (-Real.pi) Real.pi) := by
    apply ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
    exact (((hP.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
      ((hQ.continuous_fderiv (by norm_num)).clm_apply continuous_const)).continuousOn
  have h := integral2_divergence_prod_of_hasFDerivAt P Q (fderiv ℝ P) (fderiv ℝ Q)
    0 (-Real.pi) Real.pi Real.pi hP.continuous.continuousOn hQ.continuous.continuousOn
    (fun p _ => (hP.differentiable (by norm_num) p).hasFDerivAt)
    (fun p _ => (hQ.differentiable (by norm_num) p).hasFDerivAt)
    hint
  have hneg (p : Angle) : fderiv ℝ Q p (0, 1) =
      -fderiv ℝ (pullback A (1, 0)) p (0, 1) := by
    change fderiv ℝ (-pullback A (1, 0)) p (0, 1) = _
    rw [fderiv_neg]
    rfl
  simp only [hneg, ← sub_eq_add_neg] at h
  change (∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (-Real.pi)..Real.pi,
    fderiv ℝ P (θ, φ) (1, 0) - fderiv ℝ (pullback A (1, 0)) (θ, φ) (0, 1)) = 0
  rw [h]
  have hperiod (θ : ℝ) : Q (θ, Real.pi) = Q (θ, -Real.pi) := by
    simp [Q, pullback, sphere_theta, thetaTangent, sphere, circle]
  have hpole (φ : ℝ) : P (Real.pi, φ) = 0 ∧ P (0, φ) = 0 := by
    simp [P, pullback, sphere_phi, phiTangent]
  simp only [hperiod, hpole, sub_self, intervalIntegral.integral_zero, add_zero]

theorem no_global_potential (q : ℤ) (hq : q ≠ 0) :
    ¬ ∃ A : Space → Space, ContDiffOn ℝ 1 A ({0}ᶜ : Set Space) ∧
      HasCurl A (MagHK.MonopoleFlux.field q) := by
  rintro ⟨A, hA, hcurl⟩
  have hp (p : Angle) :
      fderiv ℝ (pullback A (0, 1)) p (1, 0) -
        fderiv ℝ (pullback A (1, 0)) p (0, 1) = (q : ℝ) / 2 * Real.sin p.1 := by
    rw [pullback_curvature A hA p, hcurl _ (sphere_ne_zero p), tangent_cross]
    simp only [MagHK.MonopoleFlux.field, sphere_norm, one_pow, div_one,
      real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, sphere_norm,
      one_pow, mul_one]
    ring
  have hz := closed_sphere_integral A hA
  simp only [hp, intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul] at hz
  have hi : (∫ θ in (0 : ℝ)..Real.pi, (Real.pi + Real.pi) * ((q : ℝ) / 2 * Real.sin θ)) =
      2 * Real.pi * q := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_sin]
    simp
    ring
  rw [hi] at hz
  have hreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  exact (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hreal) hz

end MagHK.MonopoleGlobalPotential
