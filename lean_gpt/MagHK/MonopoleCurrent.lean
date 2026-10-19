import MagHK.MonopoleRealization
import MagHK.MonopoleQuadrature

/-! The literal physical current of a form-domain two-particle section. The
orthonormal spherical frame and global L¹ integrability are proved from the
actual L² state and its closed covariant derivatives. No symmetry or
stationarity premise is used for this integrability statement. -/
noncomputable section
namespace MagHK.MonopoleCurrent
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.MonopoleGeometry MagHK.MonopoleQuadrature
open scoped ComplexConjugate

abbrev Space := MagHK.MonopoleQuadrature.Space

def frame (k : Fin 3) (x : Chart) : Space :=
  if k = 0 then direction x.2
  else if k = 1 then WithLp.toLp 2
    (-Real.sqrt (1 - x.2.1 ^ 2), (x.2.1 : ℂ) * circle x.2.2)
  else WithLp.toLp 2 (0, Complex.I * circle x.2.2)

theorem frame_continuous (k : Fin 3) : Continuous (frame k) := by
  fin_cases k
  · change Continuous (fun x : Chart => MonopoleQuadrature.direction x.2)
    exact direction_continuous.comp continuous_snd
  · change Continuous (fun x : Chart => WithLp.toLp 2
      (-Real.sqrt (1 - x.2.1 ^ 2), (x.2.1 : ℂ) * circle x.2.2))
    apply (WithLp.prod_continuous_toLp 2 ℝ ℂ).comp
    apply Continuous.prodMk
    · fun_prop
    · exact (Complex.continuous_ofReal.comp (continuous_fst.comp continuous_snd)).mul
        (circle_continuous.comp (continuous_snd.comp continuous_snd))
  · change Continuous (fun x : Chart => WithLp.toLp 2 (0, Complex.I * circle x.2.2))
    exact (WithLp.prod_continuous_toLp 2 ℝ ℂ).comp
      (continuous_const.prodMk (continuous_const.mul
        (circle_continuous.comp (continuous_snd.comp continuous_snd))))

theorem frame_norm (k : Fin 3) (x : Chart) (hx : x.2.1 ∈ Icc (-1 : ℝ) 1) :
    ‖frame k x‖ = 1 := by
  fin_cases k
  · exact direction_norm x.2 hx
  · change ‖WithLp.toLp 2 (-Real.sqrt (1 - x.2.1 ^ 2), (x.2.1 : ℂ) * circle x.2.2)‖ = 1
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖-Real.sqrt (1 - x.2.1 ^ 2)‖ ^ 2 + ‖(x.2.1 : ℂ) * circle x.2.2‖ ^ 2 = 1 ^ 2
    have hq : 0 ≤ 1 - x.2.1 ^ 2 := by nlinarith [hx.1, hx.2]
    simp only [norm_neg, Real.norm_eq_abs, norm_mul, Complex.norm_real,
      circle_norm, mul_one, sq_abs, Real.sq_sqrt hq]
    ring
  · change ‖WithLp.toLp 2 ((0 : ℝ), Complex.I * circle x.2.2)‖ = 1
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖(0 : ℝ)‖ ^ 2 + ‖Complex.I * circle x.2.2‖ ^ 2 = 1 ^ 2
    simp [circle_norm]

theorem frame_norm_ae (k : Fin 3) : ∀ᵐ x ∂chartMeasure, ‖frame k x‖ = 1 := by
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae angle_ae] with x hx
  exact frame_norm k x hx

def pairCurrent (S : MagneticFormSystem) (ψ : S.domain) (p : Chart × Chart) : Space :=
  ∑ k : Fin 3, (conj ((ψ : PairState) p) * S.pi 0 k ψ p).re • frame k p.1

def current (S : MagneticFormSystem) (ψ : S.domain) (x : Chart) : Space :=
  (2 : ℝ) • ∫ y, pairCurrent S ψ (x, y) ∂chartMeasure

/-- Hölder's L²×L²→L¹ fact applied to the actual weak covariant derivative. -/
theorem component_integrable (S : MagneticFormSystem) (ψ : S.domain) (k : Fin 3) :
    Integrable (fun p => (conj ((ψ : PairState) p) * S.pi 0 k ψ p).re) pairMeasure := by
  simpa only [RCLike.inner_apply'] using!
    (L2.integrable_inner (𝕜 := ℂ) (ψ : PairState) (S.pi 0 k ψ)).re

theorem frame_component_integrable (S : MagneticFormSystem) (ψ : S.domain) (k : Fin 3) :
    Integrable (fun p => (conj ((ψ : PairState) p) * S.pi 0 k ψ p).re • frame k p.1)
      pairMeasure := by
  have h := component_integrable S ψ k
  apply h.norm.mono'
  · exact h.aestronglyMeasurable.smul
      ((frame_continuous k).comp continuous_fst).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae (frame_norm_ae k)] with p hp
    rw [norm_smul, hp, mul_one]

theorem pairCurrent_integrable (S : MagneticFormSystem) (ψ : S.domain) :
    Integrable (pairCurrent S ψ) pairMeasure := by
  exact integrable_finsetSum Finset.univ (fun k _ => frame_component_integrable S ψ k)

/-- Global integrability of the physical current is a proved consequence of
finite magnetic kinetic energy. It is not an assumed property of a chosen
rotationally invariant ground state. -/
theorem current_integrable (S : MagneticFormSystem) (ψ : S.domain) :
    Integrable (current S ψ) chartMeasure :=
  (pairCurrent_integrable S ψ).integral_prod_left.smul (2 : ℝ)

/-- Constant phase covariance is derived from the actual L² representatives
and complex linearity of the closed magnetic derivative. -/
theorem pairCurrent_smul_ae (S : MagneticFormSystem) (ψ : S.domain) (c : ℂ) :
    pairCurrent S (c • ψ) =ᵐ[pairMeasure] fun p => Complex.normSq c • pairCurrent S ψ p := by
  have hψ : ∀ᵐ p ∂pairMeasure,
      ((c • ψ : S.domain) : PairState) p = c * (ψ : PairState) p := by
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] using! Lp.coeFn_smul c (ψ : PairState)
  have hpi : ∀ᵐ p ∂pairMeasure, ∀ k : Fin 3,
      S.pi 0 k (c • ψ) p = c * S.pi 0 k ψ p := by
    rw [ae_all_iff]
    intro k
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using! Lp.coeFn_smul c (S.pi 0 k ψ)
  have hm (a b : ℂ) : (conj (c * a) * (c * b)).re =
      Complex.normSq c * (conj a * b).re := by
    have he : conj (c * a) * (c * b) = (Complex.normSq c : ℂ) * (conj a * b) := by
      rw [map_mul, Complex.normSq_eq_conj_mul_self]
      ring
    rw [he]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  filter_upwards [hψ, hpi] with p hp hpk
  simp only [pairCurrent, hp, hpk, hm, Finset.smul_sum, smul_smul]

theorem current_smul_ae (S : MagneticFormSystem) (ψ : S.domain) (c : ℂ) :
    current S (c • ψ) =ᵐ[chartMeasure] fun x => Complex.normSq c • current S ψ x := by
  have h := Measure.ae_ae_of_ae_prod (pairCurrent_smul_ae S ψ c)
  filter_upwards [h] with x hx
  simp only [current]
  rw [integral_congr_ae hx, integral_smul, smul_smul, smul_smul, mul_comm]

theorem current_phase_ae (S : MagneticFormSystem) (ψ : S.domain) (c : ℂ) (hc : ‖c‖ = 1) :
    current S (c • ψ) =ᵐ[chartMeasure] current S ψ := by
  have hn : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc]; norm_num
  simpa only [hn, one_smul] using current_smul_ae S ψ c

/-- The displayed spherical frame is orthonormal on the physical chart. -/
theorem frame_inner (x : Chart) (hx : x.2.1 ∈ Icc (-1 : ℝ) 1) (i j : Fin 3) :
    inner ℝ (frame i x) (frame j x) = if i = j then 1 else 0 := by
  have hc : (circle x.2.2).re ^ 2 + (circle x.2.2).im ^ 2 = 1 := by
    have hn : Complex.normSq (circle x.2.2) = 1 := by
      rw [Complex.normSq_eq_norm_sq, circle_norm]
      norm_num
    simpa only [Complex.normSq_apply, pow_two] using hn
  by_cases hij : i = j
  · subst j
    rw [real_inner_self_eq_norm_sq, frame_norm i x hx]
    simp
  · fin_cases i <;> fin_cases j <;>
      simp_all [frame, MonopoleQuadrature.direction, spherical, cylinder,
        Complex.mul_re, Complex.mul_im]
    <;> nlinarith only [congrArg (fun r : ℝ => x.2.1 * Real.sqrt (1 - x.2.1 ^ 2) * r) hc]

theorem frame_real_sum_normSq (x : Chart) (hx : x.2.1 ∈ Icc (-1 : ℝ) 1)
    (a : Fin 3 → ℝ) : ‖∑ k : Fin 3, a k • frame k x‖ ^ 2 = ∑ k : Fin 3, a k ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    frame_inner x hx]
  simp [mul_ite, pow_two]

theorem frame_sum_normSq (x : Chart) (hx : x.2.1 ∈ Icc (-1 : ℝ) 1)
    (z : Fin 3 → ℂ) :
    ‖∑ k : Fin 3, (z k).re • frame k x‖ ^ 2 +
      ‖∑ k : Fin 3, (z k).im • frame k x‖ ^ 2 = ∑ k : Fin 3, Complex.normSq (z k) := by
  rw [frame_real_sum_normSq x hx, frame_real_sum_normSq x hx, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp [Complex.normSq_apply, pow_two]

end MagHK.MonopoleCurrent
