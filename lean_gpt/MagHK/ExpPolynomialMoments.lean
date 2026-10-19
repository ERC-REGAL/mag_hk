import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Exact exponential polynomial moments and a rational-integral enclosure.
All numerical use of this interface reduces to finite rational identities. -/
noncomputable section
namespace MagHK.ExpPolynomialMoments
open MeasureTheory Set
open scoped BigOperators

def eval {n : ℕ} (c : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin n, c i * s ^ i.val

def moment {n : ℕ} (c : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, c i * (i.val.factorial : ℝ)

theorem monomial_integrable (n : ℕ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s) * s ^ n) (Ioi 0) := by
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using
    Real.GammaIntegral_convergent (show 0 < (n : ℝ) + 1 by positivity)

theorem monomial_integral (n : ℕ) :
    (∫ s : ℝ in Ioi 0, Real.exp (-s) * s ^ n) = (n.factorial : ℝ) := by
  rw [← Real.Gamma_nat_eq_factorial n,
    Real.Gamma_eq_integral (show 0 < (n : ℝ) + 1 by positivity)]
  simp only [add_sub_cancel_right, Real.rpow_natCast]

theorem weighted_eval {n : ℕ} (c : Fin n → ℝ) (s : ℝ) :
    Real.exp (-s) * eval c s = ∑ i : Fin n, c i * (Real.exp (-s) * s ^ i.val) := by
  unfold eval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polynomial_integrable {n : ℕ} (c : Fin n → ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-s) * eval c s) (Ioi 0) := by
  simp_rw [weighted_eval]
  exact integrable_finset_sum _ (fun i _ => (monomial_integrable i.val).const_mul (c i))

theorem polynomial_integral {n : ℕ} (c : Fin n → ℝ) :
    (∫ s : ℝ in Ioi 0, Real.exp (-s) * eval c s) = moment c := by
  simp_rw [weighted_eval]
  rw [integral_finset_sum _ (fun i _ => (monomial_integrable i.val).const_mul (c i))]
  simp only [integral_const_mul, monomial_integral, moment]

/-- Polynomial identity and positivity provide exact two-sided enclosure of
an improper rational-exponential integral. -/
theorem rational_kernel_sandwich {n m : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (c : Fin n → ℝ) (d : Fin m → ℝ)
    (hi : IntegrableOn (fun s : ℝ => Real.exp (-s) / (1 + t * s)) (Ioi 0))
    (identity : ∀ s : ℝ, 0 ≤ s → (1 + t * s) * eval c s + eval d s = 1)
    (nonneg : ∀ s : ℝ, 0 ≤ s → 0 ≤ eval d s) :
    moment c ≤ (∫ s : ℝ in Ioi 0, Real.exp (-s) / (1 + t * s)) ∧
      (∫ s : ℝ in Ioi 0, Real.exp (-s) / (1 + t * s)) ≤ moment c + moment d := by
  have bounds (s : ℝ) (hs : 0 < s) :
      Real.exp (-s) * eval c s ≤ Real.exp (-s) / (1 + t * s) ∧
      Real.exp (-s) / (1 + t * s) ≤ Real.exp (-s) * eval c s + Real.exp (-s) * eval d s := by
    have hp : 0 < 1 + t * s := by positivity
    have hD : 1 ≤ 1 + t * s := by nlinarith
    have he := identity s hs.le
    have hn := nonneg s hs.le
    have hfrac : 1 / (1 + t * s) = eval c s + eval d s / (1 + t * s) := by
      apply (div_eq_iff hp.ne').mpr
      field_simp
      nlinarith
    have hl : eval c s ≤ 1 / (1 + t * s) := by
      rw [hfrac]
      have := div_nonneg hn hp.le
      linarith
    have hu : 1 / (1 + t * s) ≤ eval c s + eval d s := by
      rw [hfrac]
      have := div_le_self hn hD
      linarith
    constructor
    · simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le
    · simpa only [mul_one_div, mul_add] using mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
  constructor
  · rw [← polynomial_integral c]
    apply integral_mono_ae (polynomial_integrable c) hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (bounds s hs).1
  · rw [← polynomial_integral c, ← polynomial_integral d,
      ← integral_add (polynomial_integrable c) (polynomial_integrable d)]
    apply integral_mono_ae hi ((polynomial_integrable c).add (polynomial_integrable d))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (bounds s hs).2

end MagHK.ExpPolynomialMoments
