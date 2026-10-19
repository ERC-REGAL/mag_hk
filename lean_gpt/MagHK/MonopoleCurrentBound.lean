import MagHK.MonopoleCurrent
import MagHK.MonopoleInverse

/-! The sharp factor-two L¹ estimate for the literal marginal current. -/
noncomputable section
namespace MagHK.MonopoleCurrent
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.MonopoleGeometry MagHK.MonopoleQuadrature
open scoped ComplexConjugate BigOperators

def momentumMagnitude (S : MagneticFormSystem) (ψ : S.domain) (p : Chart × Chart) : ℝ :=
  Real.sqrt (∑ k : Fin 3, ‖S.pi 0 k ψ p‖ ^ 2)

theorem momentumMagnitude_sq (S : MagneticFormSystem) (ψ : S.domain) (p : Chart × Chart) :
    momentumMagnitude S ψ p ^ 2 = ∑ k : Fin 3, ‖S.pi 0 k ψ p‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem momentumMagnitude_memLp (S : MagneticFormSystem) (ψ : S.domain) :
    MemLp (momentumMagnitude S ψ) 2 pairMeasure := by
  have hs : AEStronglyMeasurable
      (fun p => ∑ k : Fin 3, ‖S.pi 0 k ψ p‖ ^ 2) pairMeasure := by
    have h := Finset.aestronglyMeasurable_sum Finset.univ (fun k _ =>
      (Lp.aestronglyMeasurable (S.pi 0 k ψ)).norm.pow 2)
    convert h using 1
    ext p
    simp only [Finset.sum_apply, Pi.pow_apply]
  have hm : AEStronglyMeasurable (momentumMagnitude S ψ) pairMeasure :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hs
  apply (memLp_two_iff_integrable_sq hm).mpr
  simp_rw [momentumMagnitude_sq]
  exact integrable_finsetSum _ (fun k _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (S.pi 0 k ψ))).mp
      (Lp.memLp (S.pi 0 k ψ)))

private theorem norm_square_integral (f : PairState) :
    (∫ p, ‖f p‖ ^ 2 ∂pairMeasure) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

theorem momentumMagnitude_integral_sq (S : MagneticFormSystem) (ψ : S.domain) :
    (∫ p, momentumMagnitude S ψ p ^ 2 ∂pairMeasure) =
      ∑ k : Fin 3, ‖S.pi 0 k ψ‖ ^ 2 := by
  simp_rw [momentumMagnitude_sq]
  rw [integral_finsetSum _ (fun k _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (S.pi 0 k ψ))).mp
      (Lp.memLp (S.pi 0 k ψ)))]
  simp_rw [norm_square_integral]

theorem pairCurrent_norm_bound (S : MagneticFormSystem) (ψ : S.domain) :
    ∀ᵐ p ∂pairMeasure, ‖pairCurrent S ψ p‖ ≤
      ‖(ψ : PairState) p‖ * momentumMagnitude S ψ p := by
  have hchart : ∀ᵐ p ∂pairMeasure, p.1.2.1 ∈ Icc (-1 : ℝ) 1 :=
    Measure.quasiMeasurePreserving_fst.ae
      (Measure.quasiMeasurePreserving_snd.ae angle_ae)
  filter_upwards [hchart] with p hp
  have hframe := frame_real_sum_normSq p.1 hp
    (fun k => (conj ((ψ : PairState) p) * S.pi 0 k ψ p).re)
  have hs : ‖pairCurrent S ψ p‖ ^ 2 ≤
      ‖(ψ : PairState) p‖ ^ 2 * ∑ k : Fin 3, ‖S.pi 0 k ψ p‖ ^ 2 := by
    rw [pairCurrent, hframe, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have h := sq_le_sq₀ (abs_nonneg (conj ((ψ : PairState) p) * S.pi 0 k ψ p).re)
      (norm_nonneg (conj ((ψ : PairState) p) * S.pi 0 k ψ p))
    have hb := h.mpr (Complex.abs_re_le_norm _)
    simpa only [sq_abs, norm_mul, Complex.norm_conj, mul_pow] using hb
  have hm := momentumMagnitude_sq S ψ p
  have hn : 0 ≤ momentumMagnitude S ψ p := Real.sqrt_nonneg _
  rw [← hm, ← mul_pow] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hn)).mp hs

theorem pairCurrent_integral_norm_bound (S : MagneticFormSystem) (ψ : S.domain) :
    (∫ p, ‖pairCurrent S ψ p‖ ∂pairMeasure) ≤
      ‖(ψ : PairState)‖ * Real.sqrt (∑ k : Fin 3, ‖S.pi 0 k ψ‖ ^ 2) := by
  have hm := momentumMagnitude_memLp S ψ
  have hw := (Lp.memLp (ψ : PairState)).norm
  have hprod : Integrable (fun p => ‖(ψ : PairState) p‖ * momentumMagnitude S ψ p) pairMeasure :=
    memLp_one_iff_integrable.mp (hm.mul hw)
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun p => ‖(ψ : PairState) p‖) (g := momentumMagnitude S ψ)
    (ae_of_all _ (fun p => norm_nonneg ((ψ : PairState) p)))
    (ae_of_all _ (fun p => Real.sqrt_nonneg _))
    (show MemLp (fun p => ‖(ψ : PairState) p‖) (ENNReal.ofReal 2) pairMeasure by
      simpa using hw)
    (show MemLp (momentumMagnitude S ψ) (ENNReal.ofReal 2) pairMeasure by simpa using hm)
  have hupper := integral_mono_ae (pairCurrent_integrable S ψ).norm hprod
    (pairCurrent_norm_bound S ψ)
  simp only [Real.rpow_two, norm_square_integral, momentumMagnitude_integral_sq,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg (ψ : PairState))] at hcs
  exact hupper.trans hcs

/-- This is the manuscript's displayed estimate before using normalization. -/
theorem current_integral_norm_bound (S : MagneticFormSystem) (ψ : S.domain) :
    (∫ x, ‖current S ψ x‖ ∂chartMeasure) ≤
      2 * ‖(ψ : PairState)‖ * Real.sqrt (∑ k : Fin 3, ‖S.pi 0 k ψ‖ ^ 2) := by
  have hi := (pairCurrent_integrable S ψ).norm
  have hupper : (∫ x, ‖current S ψ x‖ ∂chartMeasure) ≤
      ∫ x, 2 * (∫ y, ‖pairCurrent S ψ (x, y)‖ ∂chartMeasure) ∂chartMeasure := by
    apply integral_mono_ae (current_integrable S ψ).norm (hi.integral_prod_left.const_mul 2)
    filter_upwards [] with x
    simp only [current, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)
  rw [integral_const_mul, ← integral_prod _ hi] at hupper
  calc
    _ ≤ 2 * (∫ p, ‖pairCurrent S ψ p‖ ∂pairMeasure) := hupper
    _ ≤ 2 * (‖(ψ : PairState)‖ * Real.sqrt (∑ k : Fin 3, ‖S.pi 0 k ψ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (pairCurrent_integral_norm_bound S ψ) (by norm_num)
    _ = _ := by ring

theorem normalized_current_integral_norm_bound (S : MagneticFormSystem) (ψ : S.domain)
    (hψ : ‖(ψ : PairState)‖ = 1) :
    (∫ x, ‖current S ψ x‖ ∂chartMeasure) ≤
      2 * Real.sqrt (∑ k : Fin 3, ‖S.pi 0 k ψ‖ ^ 2) := by
  simpa only [hψ, mul_one] using current_integral_norm_bound S ψ

/-- The same exact bound for the literal Euclidean marginal integral. -/
theorem physicalCurrent_integral_norm_bound (S : MagneticFormSystem) (ψ : S.domain) :
    (∫ x : Space, ‖MagHK.MonopoleInverse.physicalCurrent S ψ x‖) ≤
      2 * ‖(ψ : PairState)‖ * Real.sqrt (∑ k : Fin 3, ‖S.pi 0 k ψ‖ ^ 2) := by
  simp_rw [MagHK.MonopoleInverse.physicalCurrent_eq]
  rw [MagHK.MonopoleInverse.integral_inverse (fun x => ‖current S ψ x‖)
    (MagHK.MonopoleInverse.current_stronglyMeasurable S ψ).norm]
  exact current_integral_norm_bound S ψ

end MagHK.MonopoleCurrent
