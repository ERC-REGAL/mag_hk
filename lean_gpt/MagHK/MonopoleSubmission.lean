import MagHK.MonopoleCounterexample
import MagHK.MonopoleDensity
import MagHK.MonopoleEndpointDomains

/-!
The October 2026 submission's monopole theorem and domain lemma, for the
same two interacting operators and physical marginals. The common radial
density and free form-domain choice are retained in the final assembly.
All background inputs already occur in the monopole proof and appendix.

The newly named angular-determinant display is `MonopoleTrial.angularDet`.
Its probability identity is `MonopoleTrial.angularDet_probability`.
The explicit charge change under conjugation and the reduction of the
correlation proof to positive charge are proved in `MonopoleTimeReversal`.
-/
noncomputable section
namespace MagHK.MonopoleSubmission
open MeasureTheory
open MagHK.MonopoleRealization MagHK.MonopoleTimeReversal MagHK.MonopoleInverse
open MagHK.MonopoleCounterexample MagHK.MonopoleEndpointDomains

/-- The display labelled `eq:angular-determinant` in the submission. -/
theorem angular_determinant_display (p q : MagHK.MonopoleTrial.Angle) :
    MagHK.MonopoleTrial.angularDet p q =
      (MagHK.MonopoleTrial.Yplus p * MagHK.MonopoleTrial.Yminus q -
        MagHK.MonopoleTrial.Yminus p * MagHK.MonopoleTrial.Yplus q) / (Real.sqrt 2 : ℂ) := by
  simp only [MagHK.MonopoleTrial.angularDet, MagHK.Slater.slaterSlice,
    MagHK.Slater.scale, MagHK.Slater.determinantSlice, div_eq_mul_inv]
  ring

/-- The closed form carried by each actual interacting operator has exactly
the free oscillator form domain at that charge. This is equality of sets of
section L² vectors, so it also applies to each constructed ground state. -/
theorem pair_form_domains (P : Pair) (forms : StandardFormDomainLibrary)
    (hardy : StandardCoulombFormLibrary) :
    (P.plus_form.domain : Set PairState) = FormDomain 1 0 ∧
      (P.minus_form.domain : Set PairState) = FormDomain (-1) 0 := by
  constructor
  · calc
      (P.plus_form.domain : Set PairState) = FormDomain 1 coulomb := by
        ext ψ
        exact P.plus_form_facts.domain_closure ψ
      _ = FormDomain 1 0 := coulomb_same_form_domain forms hardy 1
  · calc
      (P.minus_form.domain : Set PairState) = FormDomain (-1) coulomb := by
        ext ψ
        exact P.minus_form_facts.domain_closure ψ
      _ = FormDomain (-1) 0 := coulomb_same_form_domain forms hardy (-1)

/-- The interacting pair has one common measurable radial physical density,
the same form domains as the corresponding free oscillators, and compact
resolvents. The pair also carries normalization, simplicity, the explicit
gap, correlation, zero physical currents, and gauge inequivalence. -/
theorem exists_pair
    (monopole : StandardMonopoleLibrary) (exterior : StandardExteriorLibrary)
    (hardy : StandardCoulombFormLibrary) (minmax : StandardPositivePerturbationLibrary)
    (angular : MagHK.SpinChart.StandardAngularMomentumLibrary)
    (magnetic : MagHK.MonopoleCovariance.StandardMagneticActionLibrary)
    (rayleigh : MagHK.MonopoleRayleigh.StandardRayleighEqualityLibrary)
    (diagonalize : MagHK.Spin.StandardUnitaryDiagonalization)
    (isotypic : MagHK.MonopoleMultiplet.StandardIsotypicLibrary)
    (domains : MagHK.MonopoleTensorDomain.StandardCoulombOperatorLibrary)
    (tensor : MagHK.MonopoleTensorDomain.StandardSeparatedDomainLibrary)
    (spectral : StandardAntiunitaryLibrary) (friedrichs : StandardFriedrichsConjugationLibrary)
    (weak : MagHK.MonopoleCurrentZero.StandardDistributionKernelLibrary)
    (averaging : MagHK.MonopoleCurrentAveraging.StandardRotationFixedSpaceLibrary)
    (forms : StandardFormDomainLibrary) :
    ∃ P : Pair, (∃ a : ℝ → ℝ, Measurable a ∧
      physicalDensity P.positive =ᵐ[volume] (fun x => a ‖x‖) ∧
      physicalDensity P.negative =ᵐ[volume] (fun x => a ‖x‖)) ∧
      (P.plus_form.domain : Set PairState) = FormDomain 1 0 ∧
      (P.minus_form.domain : Set PairState) = FormDomain (-1) 0 ∧
      OperatorModel.CompactResolvent P.plus ∧ OperatorModel.CompactResolvent P.minus := by
  obtain ⟨G⟩ := MagHK.MonopolePositive.exists_ground monopole exterior hardy minmax angular
    magnetic rayleigh diagonalize isotypic domains tensor
  obtain ⟨u, hu, hj⟩ := MagHK.MonopoleCurrentConclusion.current_zero weak averaging
    1 G.action G.form G.operator G.facts G.form_facts G.rotations G.energy G.state
    G.eigen G.norm_one G.fixed
  obtain ⟨a, ha, hrad⟩ := MagHK.MonopoleDensity.physicalDensity_radial averaging
    1 G.action G.state G.fixed
  obtain ⟨P, hstate⟩ := of_positive_with_state spectral friedrichs G u hu hj
  rw [← hstate] at hrad
  obtain ⟨hplus, hminus⟩ := pair_form_domains P forms hardy
  exact ⟨P, ⟨a, ha, hrad, P.density_eq.trans hrad⟩, hplus, hminus,
    P.plus_facts.compact_resolvent, P.minus_facts.compact_resolvent⟩

end MagHK.MonopoleSubmission
