import MagHK.BoundedRealization
import MagHK.CartesianOrbitals
import MagHK.Cartesian
import MagHK.OperatorSpectrum

/-!
A relative, universal polar-decomposition and Weyl-theory interface. The
hypotheses are checked coefficients and actual asymptotic limits. The supplied
objects act on the actual Lebesgue L² space. Their spectrum is defined through
bounded inverses and their multiplicity through the complex eigenspace.
No statement about the manuscript's first or second eigenvalue is an input.

This file supplies no axiom or instance of the library. Providing the library
is precisely the permitted standard-operator-theory assumption. In particular,
the weak differential law and polar action below are part of that assumption,
not consequences of spectrum metadata alone.
-/
noncomputable section

namespace MagHK.PlanarSpectralLibrary
open MeasureTheory Set Filter
open MagHK.Ordering MagHK.RadialRealization MagHK.BoundedRealization
open MagHK.Noninteracting MagHK.SecondOrbital MagHK.RadialEndpoints MagHK.PotentialInfinity MagHK.Cartesian
open scoped ContDiff Topology ComplexConjugate

abbrev PlanarState := Lp ℂ 2 (volume : Measure ℂ)

/-- Smooth Cartesian coefficients with the specified azimuthal radial form. -/
structure PlanarCoefficients (a v : ℝ → ℝ)
    (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) : Prop where
  vector_smooth : ContDiff ℝ ∞ A
  scalar_smooth : ContDiff ℝ ∞ V
  vector_bounded : ∃ C : ℝ, ∀ p, ‖A p‖ ≤ C
  vector_origin : A (0, 0) = (0, 0)
  scalar_origin : V (0, 0) = v 0
  vector_radial : ∀ r p, 0 < r → radiusSq p = r ^ 2 →
    A p = (-p.2 * (a r / r), p.1 * (a r / r))
  scalar_radial : ∀ r p, 0 < r → radiusSq p = r ^ 2 → V p = v r

structure System where
  radial : RadialSystem
  H : DomainOperator PlanarState
  angularLift : ℤ → State →ₗ[ℝ] PlanarState

abbrev System.spectrum (S : System) : Set ℝ := OperatorModel.spectrum S.H
abbrev System.multiplicity (S : System) : ℝ → ℕ := OperatorModel.multiplicity S.H

/-- The literal magnetic differential expression on compactly supported tests.
The radial form of A entails div A=0. -/
def differentialExpression (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ)
    (η : ℂ → ℂ) (z : ℂ) : ℂ :=
  let dx := fun w => fderiv ℝ η w (1 : ℂ)
  let dy := fun w => fderiv ℝ η w Complex.I
  let az := A (z.re, z.im)
  show ℂ from -(fderiv ℝ dx z (1 : ℂ)) - fderiv ℝ dy z Complex.I -
    2 * Complex.I * ((az.1 : ℂ) * dx z + (az.2 : ℂ) * dy z) +
    ((az.1 ^ 2 + az.2 ^ 2 + V (z.re, z.im) : ℝ) : ℂ) * η z

structure Facts (S : System) (a v U : ℝ → ℝ)
    (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) : Prop where
  selfadjoint : OperatorModel.SelfAdjoint S.H
  sector_selfadjoint : ∀ m, OperatorModel.SelfAdjoint (S.radial.L m)
  radial_facts : StandardRadialFacts S.radial a v U
  weak_equation : ∀ ψ (hψ : ψ ∈ S.H.domain) (η : ℂ → ℂ),
    ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ z, conj (η z) * (S.H.map ⟨ψ, hψ⟩) z) =
        ∫ z, conj (differentialExpression A V η z) * ψ z
  polar_representation : ∀ m ψ, ∀ᵐ p ∂(radialMeasure.prod MagHK.CylindricalOrbitals.angularMeasure),
    (S.angularLift m ψ) (Complex.polarCoord.symm p) =
      ψ p.1 * Complex.exp (Complex.I * ((m : ℝ) * p.2 : ℝ)) /
        (Real.sqrt (2 * Real.pi) : ℝ)
  polar_isometry : ∀ m ψ, ‖S.angularLift m ψ‖ = ‖ψ‖
  polar_action : ∀ m ψ (hψ : ψ ∈ (S.radial.L m).domain),
    ∃ h : S.angularLift m ψ ∈ S.H.domain,
      S.H.map ⟨S.angularLift m ψ, h⟩ = S.angularLift m ((S.radial.L m).map ⟨ψ, hψ⟩)

/-- Standard simultaneous Friedrichs construction, polar direct sum, Weyl
essential-spectrum theorem, and compact-resolvent theorem. All fields are
quantified over general coefficient functions, not the manuscript profiles. -/
structure StandardPlanarLibrary : Prop where
  decaying : ∀ (a v U : ℝ → ℝ) (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (β : ℝ),
    CoefficientConditions a v U → PlanarCoefficients a v A V →
    Tendsto a atTop (𝓝 0) → Tendsto v atTop (𝓝 β) →
    ∃ S : System, Facts S a v U A V ∧
      PlanarSpectralFacts S.radial S.spectrum S.multiplicity β
  confining : ∀ (a v U : ℝ → ℝ) (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ),
    CoefficientConditions a v U → PlanarCoefficients a v A V →
    Tendsto v atTop atTop →
    ∃ S : System, Facts S a v U A V ∧
      ∀ β : ℝ, PlanarSpectralFacts S.radial S.spectrum S.multiplicity β

theorem bounded_planar_coefficients (t : ℝ) (ht : 0 < t) :
    PlanarCoefficients (profileA t) (regularProfileV t) (boundedVector t) (boundedScalar t) := by
  refine ⟨boundedVector_contDiff t ht.le, boundedScalar_contDiff t ht.le,
    ⟨t * Real.exp 2 + 1, boundedVector_bound t ht.le⟩,
    boundedVector_origin t, ?_, ?_, ?_⟩
  · rw [boundedScalar_origin, regularProfileV_at_zero]
    ring
  · intro r p hr hp
    exact boundedVector_radial t r p hp hr.ne'
  · intro r p hr hp
    exact (boundedScalar_agrees_off_axis t r p ht hr hp).trans
      (regularProfileV_eq t r hr.ne').symm

/-- Both levels, their simplicity, and a strict gap for the actual planar
operator, relative only to the universal standard library. -/
theorem bounded_planar_realization (library : StandardPlanarLibrary)
    (t : ℝ) (ht : 0 < t) :
    ∃ S : System,
      Facts S (profileA t) (regularProfileV t) (profileU t) (boundedVector t) (boundedScalar t) ∧
      (∀ E, E ∈ S.spectrum ∧ E ≤ 20 ↔ E = 0 ∨ E = 20) ∧
      S.multiplicity 0 = 1 ∧ S.multiplicity 20 = 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ E, 20 < E → E < 20 + ε → E ∉ S.spectrum := by
  obtain ⟨S, hS, hs⟩ := library.decaying (profileA t) (regularProfileV t) (profileU t)
    (boundedVector t) (boundedScalar t) (441 / 4) (bounded_coefficients t ht)
    (bounded_planar_coefficients t ht) (profileA_tendsto_atTop t ht)
    (regularProfileV_tendsto_atTop t ht)
  exact ⟨S, hS, bounded_planar_levels t ht S.radial hS.radial_facts
    S.spectrum S.multiplicity hs⟩

theorem bounded_zero_lift_eigen (t : ℝ) (ht : 0 < t) (S : System)
    (hS : Facts S (profileA t) (regularProfileV t) (profileU t)
      (boundedVector t) (boundedScalar t)) :
    OperatorModel.Eigen S.H 0 (S.angularLift 0 (zeroState t ht.le)) := by
  have h := hS.radial_facts.regular_solution (bounded_coefficients t ht)
    0 0 (profileF t) (zeroState t ht.le) (bounded_zero_solution t ht)
  obtain ⟨hd, he⟩ := h
  obtain ⟨hl, hle⟩ := hS.polar_action 0 _ hd
  refine ⟨hl, ?_, ?_⟩
  · intro hz
    have hn := hS.polar_isometry 0 (zeroState t ht.le)
    rw [hz, norm_zero] at hn
    exact (bounded_zero_solution t ht).nonzero (norm_eq_zero.mp hn.symm)
  · rw [hle, he, map_smul]

theorem bounded_minus_lift_eigen (t : ℝ) (ht : 0 < t) (S : System)
    (hS : Facts S (profileA t) (regularProfileV t) (profileU t)
      (boundedVector t) (boundedScalar t)) :
    OperatorModel.Eigen S.H 20 (S.angularLift (-1) (minusState t ht.le)) := by
  have h := hS.radial_facts.regular_solution (bounded_coefficients t ht)
    (-1) 20 (boundedProduct t) (minusState t ht.le) (bounded_minus_solution t ht)
  obtain ⟨hd, he⟩ := h
  obtain ⟨hl, hle⟩ := hS.polar_action (-1) _ hd
  refine ⟨hl, ?_, ?_⟩
  · intro hz
    have hn := hS.polar_isometry (-1) (minusState t ht.le)
    rw [hz, norm_zero] at hn
    exact (bounded_minus_solution t ht).nonzero (norm_eq_zero.mp hn.symm)
  · rw [hle, he, map_smul]

end MagHK.PlanarSpectralLibrary
