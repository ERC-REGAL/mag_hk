import MagHK.OperatorPreliminaries
import MagHK.MonopoleRealization
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
The standalone planar ordering lemma at its stated operator-domain level.
Unlike the concrete endpoint construction, no bounds at zero or infinity and
no separately assumed finite-energy estimates for the two known orbitals are
used here. The orbitals are positive L² eigenvectors of the actual Friedrichs
operators. Both closed-product graph identities are explicit hypotheses.

The coefficients of the displayed radial zeroth-order terms and correction
are locally integrable. This states the common-core form interpretation that
the manuscript leaves implicit. The permitted background consists of the general ground-state transform,
positive closed-form comparison, separated Sturm simplicity, and direct-sum
spectral theorem. Form energies are limits in the actual operator form norm,
so this interface does not incorrectly require separate global integrability
of kinetic and scalar-potential terms for arbitrary semibounded potentials.
-/
noncomputable section
namespace MagHK.OrderingTheorem
open MeasureTheory Set Filter
open MagHK.Ordering MagHK.RadialRealization MagHK.OperatorModel
open scoped ContDiff Topology ComplexConjugate

def Graph (T : DomainOperator State) (ψ η : State) : Prop :=
  ∃ h : ψ ∈ T.domain, T.map ⟨ψ, h⟩ = η

def Core (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ Function.support f ⊆ Ioi 0

def radialForm (a v : ℝ → ℝ) (m : ℤ) (f g : ℝ → ℂ) : ℂ :=
  ∫ r, conj (deriv f r) * deriv g r +
    ((((m : ℝ) / r + a r) ^ 2 + v r : ℝ) : ℂ) * conj (f r) * g r ∂radialMeasure

structure FriedrichsOperator (T : DomainOperator State) (a v : ℝ → ℝ) (m : ℤ) : Prop where
  potential_locally_integrable : LocallyIntegrableOn
    (fun r => ((m : ℝ) / r + a r) ^ 2 + v r) (Ioi 0) volume
  selfadjoint : OperatorModel.SelfAdjoint T
  lower_bound : ∃ b : ℝ, ∀ u : T.domain,
    -b * ‖(u : State)‖ ^ 2 ≤ inner ℝ (u : State) (T.map u)
  graph : ∀ ψ η, Graph T ψ η ↔
    MagHK.MonopoleRealization.FriedrichsGraph radialMeasure Core (radialForm a v m) ψ η

/-- Actual closed-form energy, with form-norm Cauchy approximation by vectors
in the same operator domain. -/
def FormEnergy (T : DomainOperator State) (ψ : State) (q : ℝ) : Prop :=
  ∃ b : ℝ, (∀ u : T.domain, -b * ‖(u : State)‖ ^ 2 ≤ inner ℝ (u : State) (T.map u)) ∧
  ∃ u : ℕ → T.domain, Tendsto (fun n => (u n : State)) atTop (𝓝 ψ) ∧
    Tendsto (fun n => inner ℝ (u n : State) (T.map (u n))) atTop (𝓝 q) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      |inner ℝ ((u n - u k : T.domain) : State) (T.map (u n - u k)) +
        (b + 1) * ‖((u n - u k : T.domain) : State)‖ ^ 2| < ε

theorem operator_form_energy (T : DomainOperator State) (a v : ℝ → ℝ) (m : ℤ)
    (hT : FriedrichsOperator T a v m) (ψ : State) (hψ : ψ ∈ T.domain) :
    FormEnergy T ψ (inner ℝ ψ (T.map ⟨ψ, hψ⟩)) := by
  obtain ⟨b, hb⟩ := hT.lower_bound
  refine ⟨b, hb, fun _ => ⟨ψ, hψ⟩, tendsto_const_nhds, tendsto_const_nhds, ?_⟩
  intro ε hε
  exact ⟨0, fun _ _ _ _ => by simpa using hε⟩

def FirstOrderClosure (U : ℝ → ℝ) (ψ η : State) : Prop :=
  ∃ f : ℕ → ℝ → ℂ, ∃ u w : ℕ → State,
    (∀ n, Core (f n)) ∧ (∀ n, ∀ᵐ r ∂radialMeasure, u n r = f n r) ∧
    (∀ n, ∀ᵐ r ∂radialMeasure, w n r = deriv (f n) r + (U r : ℂ) * f n r) ∧
    Tendsto u atTop (𝓝 ψ) ∧ Tendsto w atTop (𝓝 η)

/-- The literal selfadjoint operator sum on its intersection domain. The
second summand is multiplication by w, with its L² representative explicit. -/
def MultiplicationSum (B T : DomainOperator State) (w : ℝ → ℝ) : Prop :=
  ∀ ψ η, Graph B ψ η ↔ ∃ hψ : ψ ∈ T.domain, ∃ M : State,
    (∀ᵐ r ∂radialMeasure, M r = (w r : ℂ) * ψ r) ∧ T.map ⟨ψ, hψ⟩ + M = η

/-- The paper's closed D and D* and both factorizations, domains included.
The partner operator B is the Friedrichs realization with added 2W.
This records a graph identity, not a conclusion about its eigenvalues. -/
structure Factorizations (S : RadialSystem) (B : DomainOperator State)
    (a v U : ℝ → ℝ) : Prop where
  correction_locally_integrable : LocallyIntegrableOn
    (fun r => 2 * partnerCorrection a U r) (Ioi 0) volume
  D_closure : ∀ ψ η, Graph S.D ψ η ↔ FirstOrderClosure U ψ η
  adjoint : ∀ ψ η, Graph S.A ψ η ↔
    ∀ φ (hφ : φ ∈ S.D.domain), inner ℂ (S.D.map ⟨φ, hφ⟩) ψ = inner ℂ φ η
  zero_product : ∀ ψ η, Graph (S.L 0) ψ η ↔
    ∃ hD : ψ ∈ S.D.domain, ∃ hA : S.D.map ⟨ψ, hD⟩ ∈ S.A.domain,
      S.A.map ⟨S.D.map ⟨ψ, hD⟩, hA⟩ = η
  partner_product : ∀ ψ η, Graph B ψ η ↔
    ∃ hA : ψ ∈ S.A.domain, ∃ hD : S.A.map ⟨ψ, hA⟩ ∈ S.D.domain,
      S.D.map ⟨S.A.map ⟨ψ, hA⟩, hD⟩ = η
  partner_selfadjoint : OperatorModel.SelfAdjoint B
  partner_sum : MultiplicationSum B (S.L (-1)) (fun r => 2 * partnerCorrection a U r)

structure PositiveEigenfunction (T : DomainOperator State) (E : ℝ)
    (u : ℝ → ℝ) (ψ : State) : Prop where
  positive : ∀ r, 0 < r → 0 < u r
  represented : ∀ᵐ r ∂radialMeasure, ψ r = (u r : ℂ)
  eigen : OperatorModel.Eigen T E ψ

def remainder (u : ℝ → ℝ) (ψ : State) (dψ : ℝ → ℂ) : ℝ :=
  ∫ r, ‖dψ r - (deriv u r / u r : ℂ) * ψ r‖ ^ 2 ∂radialMeasure

/-- Universal closed-form laws for arbitrary radial Friedrichs problems.
The ground transform is an integral identity. The comparison field is the
positive multiplication-form theorem on the common compact smooth core. -/
structure StandardRadialFormLibrary : Prop where
  positive_sum_friedrichs : ∀ T B a v m w,
    FriedrichsOperator T a v m → OperatorModel.SelfAdjoint B →
    LocallyIntegrableOn w (Ioi 0) volume → (∀ r, 0 < r → 0 ≤ w r) →
    MultiplicationSum B T w → FriedrichsOperator B a (fun r => v r + w r) m
  ground_transform : ∀ T a v m E u ξ,
    FriedrichsOperator T a v m → PositiveEigenfunction T E u ξ →
    ∀ ψ q, FormEnergy T ψ q → ∃ u' : ℝ → ℝ, ∃ dψ : ℝ → ℂ,
      ContDiffOn ℝ 1 u' (Ioi 0) ∧ (∀ r, 0 < r → 0 < u' r) ∧
      (∀ᵐ r ∂radialMeasure, ξ r = (u' r : ℂ)) ∧
      IsWeakDerivative ψ dψ ∧ q = E * mass ψ + remainder u' ψ dψ
  form_difference : ∀ T₁ T₂ a₁ v₁ m₁ a₂ v₂ m₂ w,
    FriedrichsOperator T₁ a₁ v₁ m₁ → FriedrichsOperator T₂ a₂ v₂ m₂ →
    (∀ r, 0 < r → 0 ≤ w r) →
    (∀ r, 0 < r → ((m₁ : ℝ) / r + a₁ r) ^ 2 + v₁ r =
      ((m₂ : ℝ) / r + a₂ r) ^ 2 + v₂ r + w r) →
    ∀ ψ q, FormEnergy T₁ ψ q → ∃ q₀ : ℝ, FormEnergy T₂ ψ q₀ ∧
      Integrable (fun r => w r * density ψ r) radialMeasure ∧ q = q₀ + multiplier w ψ
  sturm_simplicity : ∀ T a v m E ψ φ,
    FriedrichsOperator T a v m → OperatorModel.Eigen T E ψ →
    (∃ hφ : φ ∈ T.domain, T.map ⟨φ, hφ⟩ = E • φ) → ∃ c : ℂ, φ = c • ψ

/-- A literal unitary direct sum, including the complete operator graph. -/
structure DirectSum (H : DomainOperator PlanarSpectralLibrary.PlanarState)
    (S : RadialSystem) where
  unitary : PlanarSpectralLibrary.PlanarState ≃ₗᵢ[ℂ] lp (fun _ : ℤ => State) 2
  graph : ∀ ψ η,
    (∃ hψ : ψ ∈ H.domain, H.map ⟨ψ, hψ⟩ = η) ↔
    ∀ m, Graph (S.L m) (unitary ψ m) (unitary η m)

/-- General direct-sum spectral theory below the actual essential spectrum.
No selected energy, radial ordering, or selected eigenvalue gap is an input. -/
def StandardDirectSumLibrary : Prop :=
  ∀ H S a v, OperatorModel.SelfAdjoint H →
    (∀ m, FriedrichsOperator (S.L m) a v m) → DirectSum H S →
    ∀ Λ : ℝ, OperatorPreliminaries.essentialSpectrum H ⊆ Ici Λ →
      BoundedRealization.PlanarSpectralFacts S (spectrum H) (multiplicity H) Λ

private theorem energy_eigen (ψ : State) (E : ℝ) :
    inner ℝ ψ (E • ψ) = E * mass ψ := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq, mass_eq_norm_sq]

theorem ground_lower (library : StandardRadialFormLibrary)
    (T : DomainOperator State) (a v u : ℝ → ℝ) (m : ℤ) (E : ℝ)
    (hT : FriedrichsOperator T a v m) (ξ : State) (hu : PositiveEigenfunction T E u ξ)
    (ψ : State) (q : ℝ) (hq : FormEnergy T ψ q) : E * mass ψ ≤ q := by
  obtain ⟨u', dψ, _, _, _, _, he⟩ := library.ground_transform T a v m E u ξ hT hu ψ q hq
  rw [he]
  have hnon : 0 ≤ remainder u' ψ dψ := integral_nonneg (fun _ => sq_nonneg _)
  linarith

theorem ordering_data (library : StandardRadialFormLibrary)
    (S : RadialSystem) (B : DomainOperator State) (a v U u₀ u₁ : ℝ → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (hL : ∀ m, FriedrichsOperator (S.L m) a v m)
    (hf : Factorizations S B a v U) (ψ₀ ψ₁ : State)
    (hu₀ : PositiveEigenfunction (S.L 0) 0 u₀ ψ₀)
    (hu₁ : PositiveEigenfunction (S.L (-1)) lam u₁ ψ₁)
    (ha : ∀ r, 0 < r → 0 < r * a r ∧ r * a r < 1)
    (hW : ∀ r, 0 < r → 0 < partnerCorrection a U r) :
    RadialOrderingData (RadialRealization.Eigen S) lam := by
  have hBfri := library.positive_sum_friedrichs (S.L (-1)) B a v (-1)
    (fun r => 2 * partnerCorrection a U r) (hL (-1)) hf.partner_selfadjoint
    hf.correction_locally_integrable
    (fun r hr => by have := hW r hr; positivity) hf.partner_sum
  refine ⟨hlam, ⟨ψ₀, hu₀.eigen⟩, ⟨ψ₁, hu₁.eigen⟩, ?_, ?_, ?_⟩
  · intro E he
    obtain ⟨ψ, hψ, hne, heq⟩ := he
    obtain ⟨hD, hA, hprod⟩ := (hf.zero_product ψ (E • ψ)).mp ⟨hψ, heq⟩
    let φ : State := S.D.map ⟨ψ, hD⟩
    have hadj := (hf.adjoint φ (E • ψ)).mp ⟨hA, hprod⟩ ψ hD
    have hmass : E * mass ψ = mass φ := by
      change inner ℂ φ φ = inner ℂ ψ (E • ψ) at hadj
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
        inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hadj
      have hh : ‖φ‖ ^ 2 = E * ‖ψ‖ ^ 2 := by exact_mod_cast hadj
      simpa only [mass_eq_norm_sq] using hh.symm
    refine ⟨mass ψ, mass φ, mass_pos ψ hne, by rw [mass_eq_norm_sq]; positivity, hmass, ?_⟩
    intro hφmass
    have hφne : φ ≠ 0 := by
      intro hz
      rw [mass_eq_norm_sq, hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hφmass
      exact lt_irrefl 0 hφmass
    obtain ⟨hAD, htransfer⟩ := eigenvector_transfer S.D S.A ψ E hD hA hprod
    obtain ⟨hB, hBeq⟩ := (hf.partner_product φ (E • φ)).mpr ⟨hA, hAD, htransfer⟩
    have henergy := operator_form_energy B a _ (-1) hBfri φ hB
    rw [hBeq, energy_eigen] at henergy
    obtain ⟨q, hq, hint, hsplit⟩ := library.form_difference B (S.L (-1)) a
      (fun r => v r + 2 * partnerCorrection a U r) (-1) a v (-1)
      (fun r => 2 * partnerCorrection a U r) hBfri (hL (-1))
      (fun r hr => by have := hW r hr; positivity) (fun _ _ => by ring) φ _ henergy
    have hδ : 0 < multiplier (fun r => 2 * partnerCorrection a U r) φ :=
      multiplier_pos _ φ (fun r hr => by have := hW r hr; positivity) hφne hint
    refine ⟨q, multiplier (fun r => 2 * partnerCorrection a U r) φ / 2,
      ground_lower library _ a v u₁ (-1) lam (hL (-1)) ψ₁ hu₁ φ q hq,
      by positivity, ?_⟩
    linarith
  · intro E he
    obtain ⟨ψ, hψ, hne, heq⟩ := he
    have henergy := operator_form_energy (S.L (-1)) a v (-1) (hL (-1)) ψ hψ
    rw [heq, energy_eigen] at henergy
    exact ⟨mass ψ, E * mass ψ, mass_pos ψ hne,
      ground_lower library _ a v u₁ (-1) lam (hL (-1)) ψ₁ hu₁ ψ _ henergy, rfl⟩
  · intro m E hm0 hm1 he
    obtain ⟨ψ, hψ, hne, heq⟩ := he
    have hdiff : ∀ r, 0 < r → 0 < angularDifference a m r := by
      intro r hr
      exact all_other_sector_difference_pos m (a r) r hr (ha r hr).1 (ha r hr).2 hm0 hm1
    have henergy := operator_form_energy (S.L m) a v m (hL m) ψ hψ
    rw [heq, energy_eigen] at henergy
    obtain ⟨q, hq, hint, hsplit⟩ := library.form_difference (S.L m) (S.L (-1))
      a v m a v (-1) (angularDifference a m) (hL m) (hL (-1))
      (fun r hr => (hdiff r hr).le) (fun r _ => by unfold angularDifference; norm_num; ring)
      ψ _ henergy
    exact ⟨mass ψ, q, multiplier (angularDifference a m) ψ, mass_pos ψ hne,
      ground_lower library _ a v u₁ (-1) lam (hL (-1)) ψ₁ hu₁ ψ q hq,
      multiplier_pos _ ψ hdiff hne hint, hsplit⟩

/-- The standalone lemma for locally integrable radial expressions. Its known
positive L² eigenfunctions, closed-product domains, multiplier conditions and
essential-spectrum bound are explicit. The coefficient local-integrability
conditions state the technical common-core interpretation of the manuscript.
The analytic inputs are the two universal libraries above. -/
theorem lowest_two_planar_levels (radial : StandardRadialFormLibrary)
    (direct : StandardDirectSumLibrary)
    (H : DomainOperator PlanarSpectralLibrary.PlanarState)
    (S : RadialSystem) (B : DomainOperator State) (a v U u₀ u₁ : ℝ → ℝ)
    (lam Λ : ℝ) (hlam : 0 < lam) (hΛ : lam < Λ)
    (hH : OperatorModel.SelfAdjoint H) (hds : DirectSum H S)
    (hess : OperatorPreliminaries.essentialSpectrum H ⊆ Ici Λ)
    (hL : ∀ m, FriedrichsOperator (S.L m) a v m)
    (hf : Factorizations S B a v U) (ψ₀ ψ₁ : State)
    (hu₀ : PositiveEigenfunction (S.L 0) 0 u₀ ψ₀)
    (hu₁ : PositiveEigenfunction (S.L (-1)) lam u₁ ψ₁)
    (_hU : ∀ r, 0 < r → U r = -deriv u₀ r / u₀ r)
    (ha : ∀ r, 0 < r → 0 < r * a r ∧ r * a r < 1)
    (hW : ∀ r, 0 < r → 0 < partnerCorrection a U r) :
    (∀ E, E ∈ spectrum H ∧ E ≤ lam ↔ E = 0 ∨ E = lam) ∧
    multiplicity H 0 = 1 ∧ multiplicity H lam = 1 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ E, lam < E → E < lam + ε → E ∉ spectrum H := by
  have ho := ordering_data radial S B a v U u₀ u₁ lam hlam hL hf ψ₀ ψ₁ hu₀ hu₁ ha hW
  have hs := direct H S a v hH hL hds Λ hess
  have hsimple : ∀ m E, RadialRealization.Eigen S m E →
      BoundedRealization.SimpleRadialEigenline S m E := by
    intro m E he
    obtain ⟨ψ, hψ, hne, heq⟩ := he
    exact ⟨ψ, hψ, hne, heq, fun φ hφ hφE =>
      radial.sturm_simplicity (S.L m) a v m E ψ φ (hL m) ⟨hψ, hne, heq⟩ ⟨hφ, hφE⟩⟩
  refine ⟨planar_spectrum_below_second ho hs.discrete hΛ, ?_, ?_,
    planar_strict_gap ho hs.discrete hΛ⟩
  · exact hs.dimension_of_single_eigenline 0 0 (fun _ he => unique_sector_at_zero ho he)
      (hsimple 0 0 ho.zero_state)
  · exact hs.dimension_of_single_eigenline lam (-1) (fun _ he => unique_sector_at_lambda ho he)
      (hsimple (-1) lam ho.minus_one_state)

end MagHK.OrderingTheorem
