import MagHK.SpinChart
import MagHK.MonopolePairLaw

/-! The coordinate reconstruction linking the literal Hopf pullback with
actual spatial rotations. No chart or coordinate identity is assumed. -/
noncomputable section
namespace MagHK.SpinChart
open MeasureTheory Set Matrix
open MagHK.MonopoleRealization MagHK.MonopoleTrial
open scoped ComplexConjugate Matrix
set_option maxHeartbeats 1000000

theorem spinor_zero (p : Angle) : spinor p 0 = spinorPlus p := rfl

theorem spinor_one (p : Angle) : spinor p 1 = spinorMinus p := by
  simp [spinor, spinorMinus, MagHK.CylindricalOrbitals.phase, MagHK.Spin.phase,
    ← Complex.exp_conj, mul_comm]

theorem spinor_normSq (p : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    Complex.normSq (spinor p 0) + Complex.normSq (spinor p 1) = 1 := by
  rw [spinor_zero, spinor_one]
  exact spinor_normalized p hp

theorem hopf_spinor (p : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    hopf (spinor p) = MagHK.MonopoleQuadrature.direction p := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change Complex.normSq (spinor p 0) - Complex.normSq (spinor p 1) = 1 * p.1
    rw [spinor_zero, spinor_one, spinorPlus_normSq p hp, spinorMinus_normSq p hp]
    ring
  · change 2 * spinor p 0 * conj (spinor p 1) = _
    rw [spinor_zero, spinor_one, MagHK.MonopolePairLaw.direction_complex p hp]
    rfl

theorem unitary_normSq (U : MagHK.Spin.Group) (z : Fin 2 → ℂ) :
    Complex.normSq (U.val.mulVec z 0) + Complex.normSq (U.val.mulVec z 1) =
      Complex.normSq (z 0) + Complex.normSq (z 1) := by
  have he : star (U.val *ᵥ z) ⬝ᵥ (U.val *ᵥ z) = star z ⬝ᵥ z := by
    rw [Matrix.star_mulVec, dotProduct_mulVec, Matrix.vecMul_vecMul]
    have hu : U.val.conjTranspose * U.val = 1 := U.property.1.1
    rw [hu, Matrix.vecMul_one]
  have hnorm (w : Fin 2 → ℂ) : star w ⬝ᵥ w =
      ((Complex.normSq (w 0) + Complex.normSq (w 1) : ℝ) : ℂ) := by
    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_add]
  rw [hnorm, hnorm] at he
  exact Complex.ofReal_injective he

def angleOfSpinor (z : Fin 2 → ℂ) : Angle :=
  (2 * Complex.normSq (z 0) - 1, -Complex.arg (z 1 / z 0))

theorem angleOfSpinor_mem (z : Fin 2 → ℂ)
    (hz : Complex.normSq (z 0) + Complex.normSq (z 1) = 1) :
    (angleOfSpinor z).1 ∈ Icc (-1 : ℝ) 1 := by
  have h₀ := Complex.normSq_nonneg (z 0)
  have h₁ := Complex.normSq_nonneg (z 1)
  change -1 ≤ 2 * Complex.normSq (z 0) - 1 ∧ 2 * Complex.normSq (z 0) - 1 ≤ 1
  constructor <;> linarith

theorem phase_arg (z : ℂ) (hz : z ≠ 0) :
    MagHK.Spin.phase (Complex.arg z) = z / (‖z‖ : ℂ) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  apply (eq_div_iff hn).mpr
  simpa [MagHK.Spin.phase, mul_comm] using Complex.norm_mul_exp_arg_mul_I z

theorem reconstructed_spinor (z : Fin 2 → ℂ)
    (hz : Complex.normSq (z 0) + Complex.normSq (z 1) = 1) (h₀ : z 0 ≠ 0) :
    ∀ i, unitPhase (z 0) * spinor (angleOfSpinor z) i = z i := by
  have ha : Real.sqrt ((1 + (angleOfSpinor z).1) / 2) = ‖z 0‖ := by
    have he : (1 + (angleOfSpinor z).1) / 2 = ‖z 0‖ ^ 2 := by
      dsimp [angleOfSpinor]
      rw [Complex.normSq_eq_norm_sq]
      ring
    rw [he, Real.sqrt_sq (norm_nonneg _)]
  have hb : Real.sqrt ((1 - (angleOfSpinor z).1) / 2) = ‖z 1‖ := by
    have he : (1 - (angleOfSpinor z).1) / 2 = ‖z 1‖ ^ 2 := by
      dsimp [angleOfSpinor]
      rw [← Complex.normSq_eq_norm_sq]
      linarith
    rw [he, Real.sqrt_sq (norm_nonneg _)]
  intro i
  fin_cases i
  · simp [spinor, ha, unitPhase, h₀]
  · change unitPhase (z 0) * (MagHK.Spin.phase (-(angleOfSpinor z).2) *
        (Real.sqrt ((1 - (angleOfSpinor z).1) / 2) : ℂ)) = z 1
    rw [hb]
    by_cases h₁ : z 1 = 0
    · simp [h₁]
    · have hdiv : z 1 / z 0 ≠ 0 := div_ne_zero h₁ h₀
      have hn₀ : (‖z 0‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h₀)
      have hn₁ : (‖z 1‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h₁)
      simp only [angleOfSpinor, neg_neg, phase_arg _ hdiv, norm_div, Complex.ofReal_div,
        unitPhase, if_neg h₀]
      field_simp
      <;> ring

theorem hopf_phase (c : ℂ) (hc : ‖c‖ = 1) (z : Fin 2 → ℂ) :
    hopf (fun i => c * z i) = hopf z := by
  have hn : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc]; norm_num
  have hp : c * conj c = 1 := by
    rw [Complex.mul_conj]
    exact_mod_cast hn
  apply WithLp.ofLp_injective
  apply Prod.ext
  · simp [hopf, Complex.normSq_mul, hn]
  · change 2 * (c * z 0) * conj (c * z 1) = 2 * z 0 * conj (z 1)
    rw [map_mul]
    calc
      _ = (c * conj c) * (2 * z 0 * conj (z 1)) := by ring
      _ = _ := by rw [hp, one_mul]

theorem direction_angleOfSpinor (z : Fin 2 → ℂ)
    (hz : Complex.normSq (z 0) + Complex.normSq (z 1) = 1) :
    MagHK.MonopoleQuadrature.direction (angleOfSpinor z) = hopf z := by
  rw [← hopf_spinor _ (angleOfSpinor_mem z hz)]
  by_cases h₀ : z 0 = 0
  · have h₁ : Complex.normSq (z 1) = 1 := by simpa [h₀] using hz
    apply WithLp.ofLp_injective
    apply Prod.ext
    · simp [hopf, spinor, angleOfSpinor, h₀, h₁, MagHK.Spin.phase]
    · simp [hopf, spinor, angleOfSpinor, h₀, MagHK.Spin.phase]
  · have he : (fun i => unitPhase (z 0) * spinor (angleOfSpinor z) i) = z :=
      funext (reconstructed_spinor z hz h₀)
    rw [← hopf_phase (unitPhase (z 0)) (unitPhase_norm _) _, he]

def point (x : Chart) : Space := x.1 • MagHK.MonopoleQuadrature.direction x.2

theorem moved_point (q : ℤ) (R : AngularMomentumAction q) (U : MagHK.Spin.Group)
    (x : Chart) (hx : x.2.1 ∈ Icc (-1 : ℝ) 1) :
    point (movedChart U x) = R.rotation U⁻¹ (point x) := by
  have hz : Complex.normSq (movedSpinor U x.2 0) +
      Complex.normSq (movedSpinor U x.2 1) = 1 :=
    (unitary_normSq U⁻¹ (spinor x.2)).trans (spinor_normSq x.2 hx)
  change x.1 • MagHK.MonopoleQuadrature.direction (angleOfSpinor (movedSpinor U x.2)) = _
  rw [direction_angleOfSpinor _ hz]
  change x.1 • hopf ((U⁻¹).val.mulVec (spinor x.2)) = _
  rw [R.rotation_hopf, hopf_spinor x.2 hx]
  exact ((R.rotation U⁻¹).map_smul x.1 (MagHK.MonopoleQuadrature.direction x.2)).symm

end MagHK.SpinChart
