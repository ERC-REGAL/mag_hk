import MagHK.MonopoleRealization

/-!
The exact magnetic Hardy and Coulomb form estimates on actual two-particle
section L². The universal external premise is the usual diamagnetic Hardy
inequality in the relative coordinate, with constant 2 multiplying the sum
of the two covariant kinetic energies. It ranges over all charges, form
realizations, potentials and form vectors. Cauchy–Schwarz and Young's inequality
then give the manuscript's explicit Coulomb estimate with constant 1/(2ε).
-/
noncomputable section
namespace MagHK.MonopoleHardy
open MeasureTheory
open MagHK.Monopole MagHK.MonopoleTrial MagHK.MonopoleRealization

def kinetic (S : MagneticFormSystem) (ψ : S.domain) : ℝ :=
  ∑ i : Fin 2, ∑ k : Fin 3, ‖S.pi i k ψ‖ ^ 2

theorem kinetic_nonnegative (S : MagneticFormSystem) (ψ : S.domain) :
    0 ≤ kinetic S ψ := by unfold kinetic; positivity

/-- The closed multiplication operator by the literal inverse pair distance
is bounded from the magnetic homogeneous H¹ form space to L². This is the
general magnetic Hardy theorem, independent of any chosen eigenfunction. -/
def StandardMagneticHardyLibrary : Prop :=
  ∀ (q : ℤ) (W : Chart × Chart → ℝ) (F : FermionSystem) (S : MagneticFormSystem),
    MagneticFormFacts S F q W → ∀ ψ : S.domain, ∃ χ : PairState,
      (∀ᵐ p ∂pairMeasure, χ p = (coulomb p : ℂ) * (ψ : PairState) p) ∧
      ‖χ‖ ^ 2 ≤ 2 * kinetic S ψ

private theorem weighted_inner (ψ χ : PairState)
    (hχ : ∀ᵐ p ∂pairMeasure, χ p = (coulomb p : ℂ) * ψ p) :
    ∀ᵐ p ∂pairMeasure, inner ℝ (ψ p) (χ p) = coulomb p * Complex.normSq (ψ p) := by
  filter_upwards [hχ] with p hp
  rw [hp]
  change inner ℝ (ψ p) ((coulomb p) • ψ p) = coulomb p * Complex.normSq (ψ p)
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq]

private theorem weighted_square (ψ χ : PairState)
    (hχ : ∀ᵐ p ∂pairMeasure, χ p = (coulomb p : ℂ) * ψ p) :
    ∀ᵐ p ∂pairMeasure, inner ℝ (χ p) (χ p) =
      coulomb p ^ 2 * Complex.normSq (ψ p) := by
  filter_upwards [hχ] with p hp
  rw [real_inner_self_eq_norm_sq, hp, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.normSq_eq_norm_sq]

theorem magnetic_hardy (library : StandardMagneticHardyLibrary)
    (q : ℤ) (W : Chart × Chart → ℝ) (F : FermionSystem) (S : MagneticFormSystem)
    (hS : MagneticFormFacts S F q W) (ψ : S.domain) :
    Integrable (fun p => coulomb p ^ 2 * Complex.normSq ((ψ : PairState) p)) pairMeasure ∧
    (∫ p, coulomb p ^ 2 * Complex.normSq ((ψ : PairState) p) ∂pairMeasure) ≤
      2 * kinetic S ψ := by
  obtain ⟨χ, hχ, hh⟩ := library q W F S hS ψ
  have he := weighted_square (ψ : PairState) χ hχ
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) χ χ).congr he, ?_⟩
  calc
    _ = inner ℝ χ χ := (integral_congr_ae he).symm
    _ = ‖χ‖ ^ 2 := real_inner_self_eq_norm_sq χ
    _ ≤ 2 * kinetic S ψ := hh

theorem coulomb_cauchy_schwarz (library : StandardMagneticHardyLibrary)
    (q : ℤ) (W : Chart × Chart → ℝ) (F : FermionSystem) (S : MagneticFormSystem)
    (hS : MagneticFormFacts S F q W) (ψ : S.domain) :
    Integrable (fun p => coulomb p * Complex.normSq ((ψ : PairState) p)) pairMeasure ∧
    |∫ p, coulomb p * Complex.normSq ((ψ : PairState) p) ∂pairMeasure| ≤
      Real.sqrt 2 * ‖(ψ : PairState)‖ * Real.sqrt (kinetic S ψ) := by
  obtain ⟨χ, hχ, hh⟩ := library q W F S hS ψ
  have he := weighted_inner (ψ : PairState) χ hχ
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) (ψ : PairState) χ).congr he, ?_⟩
  have hb : ‖χ‖ ≤ Real.sqrt 2 * Real.sqrt (kinetic S ψ) := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hk := Real.sq_sqrt (kinetic_nonnegative S ψ)
    have hn : 0 ≤ Real.sqrt 2 * Real.sqrt (kinetic S ψ) := by positivity
    nlinarith [norm_nonneg χ]
  calc
    _ = |inner ℝ (ψ : PairState) χ| := congrArg abs (integral_congr_ae he).symm
    _ ≤ ‖(ψ : PairState)‖ * ‖χ‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖(ψ : PairState)‖ * (Real.sqrt 2 * Real.sqrt (kinetic S ψ)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

theorem coulomb_explicit_form_bound (library : StandardMagneticHardyLibrary)
    (q : ℤ) (W : Chart × Chart → ℝ) (F : FermionSystem) (S : MagneticFormSystem)
    (hS : MagneticFormFacts S F q W) (ψ : S.domain) (ε : ℝ) (hε : 0 < ε) :
    |∫ p, coulomb p * Complex.normSq ((ψ : PairState) p) ∂pairMeasure| ≤
      ε * kinetic S ψ + ‖(ψ : PairState)‖ ^ 2 / (2 * ε) := by
  calc
    _ ≤ Real.sqrt 2 * ‖(ψ : PairState)‖ * Real.sqrt (kinetic S ψ) :=
      (coulomb_cauchy_schwarz library q W F S hS ψ).2
    _ ≤ ε * kinetic S ψ + (1 / (2 * ε)) * ‖(ψ : PairState)‖ ^ 2 :=
      coulomb_form_young_bound _ _ _ (kinetic_nonnegative S ψ) hε
    _ = _ := by ring

end MagHK.MonopoleHardy
