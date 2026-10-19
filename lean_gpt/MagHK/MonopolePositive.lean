import MagHK.MonopoleGround
import MagHK.MonopoleNonSlater
import MagHK.MonopoleRayleigh
import MagHK.MonopoleRotationPotential

/-! The actual positive-charge interacting ground state, its singlet symmetry,
and its non-Slater character, assembled from the universal background inputs. -/
noncomputable section
namespace MagHK.MonopolePositive
open MeasureTheory
open MagHK.MonopoleRealization MagHK.SpinChart MagHK.MonopoleCovariance
open MagHK.MonopoleRayleigh MagHK.MonopoleMultiplet MagHK.MonopoleTensorDomain

/-- All fields concern the same normalized state and the same Friedrichs operator. -/
structure Ground where
  operator : FermionSystem
  energy : ℝ
  state : FermionState
  form : MagneticFormSystem
  facts : FermionFacts operator 1 coulomb
  form_facts : MagneticFormFacts form operator 1 coulomb
  action : AngularMomentumAction 1
  rotations : MagneticRotations 1 action form operator coulomb form_facts
  eigen : OperatorModel.Eigen operator energy state
  norm_one : ‖state‖ = 1
  ground : GroundState operator energy (fun p => (state : PairState) p)
  gap : SpectralGap operator energy (MagHK.Monopole.freeGap - MagHK.Monopole.coulombBound)
  fixed : ∀ U, action.pair U state = state
  not_slater : ¬ IsSlater state

theorem exists_ground
    (monopole : StandardMonopoleLibrary) (exterior : StandardExteriorLibrary)
    (hardy : StandardCoulombFormLibrary) (minmax : StandardPositivePerturbationLibrary)
    (angular : StandardAngularMomentumLibrary)
    (magnetic : StandardMagneticActionLibrary)
    (rayleigh : StandardRayleighEqualityLibrary)
    (diagonalize : MagHK.Spin.StandardUnitaryDiagonalization)
    (isotypic : StandardIsotypicLibrary)
    (domains : StandardCoulombOperatorLibrary) (tensor : StandardSeparatedDomainLibrary) :
    Nonempty Ground := by
  obtain ⟨F, E, E₁, ψ, hF, hψ, hn, hg, hgap, _, _, _⟩ :=
    interacting_ground_state monopole exterior hardy minmax
  obtain ⟨S, hS⟩ := hF.form_realization
  obtain ⟨R⟩ := angular 1
  have hW := coulomb_rotation_invariant 1 R
  obtain ⟨A⟩ := magnetic 1 R S F coulomb hS hW
  have hfixed := ground_singlet rayleigh diagonalize 1 coulomb R F hF S hS A hW
    E hg.2.1 ψ hψ hg.2.2
  obtain ⟨H, F₀, _, hF₀, _, _⟩ := free_ground_state monopole exterior
  have hns := MagHK.MonopoleSeparation.singlet_not_slater isotypic domains tensor
    R F₀ F hF₀ hF E ψ hψ hfixed
  exact ⟨⟨F, E, ψ, S, hF, hS, R, A, hψ, hn, hg, hgap, hfixed, hns⟩⟩

theorem Ground.gap_numeric (G : Ground) :
    ∀ e ∈ OperatorModel.spectrum G.operator, e ≠ G.energy →
      G.energy + (533 / 500 : ℝ) < e := by
  intro e he hne
  have h := G.gap e he hne
  have hn := MagHK.Monopole.explicit_gap_lower_bound
  linarith

end MagHK.MonopolePositive
