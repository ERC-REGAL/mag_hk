import MagHK.ManyBodyTimeReversal

/-! The arbitrary-particle density in the October 2026 preliminaries.
Fubini and the actual first-coordinate splitting give integrability and
particle-number normalization. No new background theorem is assumed. -/
noncomputable section
namespace MagHK.ManyBodyTimeReversal
open MeasureTheory

theorem normSq_cons_integrable (N : ℕ) (f : Configuration (N + 1) → ℂ)
    (hf : MemLp f 2) :
    Integrable (fun x : Point × Configuration N => Complex.normSq (f (Fin.cons x.1 x.2))) := by
  have hi : Integrable (fun x => Complex.normSq (f x)) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      hf.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => Point) 0).symm
  have hj := hm.integrable_comp_of_integrable hi
  simpa [Function.comp_def, MeasurableEquiv.piFinSuccAbove,
    Fin.insertNthEquiv, Fin.insertNth_zero'] using hj

theorem density_nonnegative (N : ℕ) (f : Configuration (N + 1) → ℂ) (x : Point) :
    0 ≤ density N f x := by
  unfold density
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun _ => Complex.normSq_nonneg _)

theorem density_integrable (N : ℕ) (f : Configuration (N + 1) → ℂ)
    (hf : MemLp f 2) : Integrable (density N f) := by
  exact (normSq_cons_integrable N f hf).integral_prod_left.const_mul _

theorem density_mass (N : ℕ) (f : Configuration (N + 1) → ℂ)
    (hf : MemLp f 2) :
    (∫ x, density N f x) = (N + 1 : ℝ) * ∫ x, Complex.normSq (f x) := by
  have hi := normSq_cons_integrable N f hf
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => Point) 0).symm
  have he : (∫ x : Point × Configuration N, Complex.normSq (f (Fin.cons x.1 x.2))) =
      ∫ x, Complex.normSq (f x) := by
    simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero'] using
      hm.integral_comp' (fun x => Complex.normSq (f x))
  unfold density
  rw [integral_const_mul, ← integral_prod _ hi, ← Measure.volume_eq_prod, he]

theorem normalized_density_mass (N : ℕ) (f : Configuration (N + 1) → ℂ)
    (hf : MemLp f 2) (hn : (∫ x, Complex.normSq (f x)) = 1) :
    (∫ x, density N f x) = (N + 1 : ℝ) := by
  rw [density_mass N f hf, hn, mul_one]

end MagHK.ManyBodyTimeReversal
