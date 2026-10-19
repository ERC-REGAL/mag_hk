import MagHK.MonopoleFormCovariance
import MagHK.MonopoleSinglet

/-! Equality in the bottom Rayleigh bound turns the proved form symmetry into a singlet. -/
noncomputable section
namespace MagHK.MonopoleRayleigh
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.SpinChart MagHK.MonopoleCovariance

/-- The standard equality case of the Rayleigh principle for the actual
Friedrichs form, uniform in the charge, scalar interaction and form vector. -/
def StandardRayleighEqualityLibrary : Prop :=
  ∀ q W (F : FermionSystem), FermionFacts F q W →
    ∀ (S : MagneticFormSystem) (hS : MagneticFormFacts S F q W) (E : ℝ),
    (∀ e ∈ OperatorModel.spectrum F, E ≤ e) →
    ∀ φ : S.domain, (φ : PairState) ≠ 0 →
      (formPairing S W φ φ).re = E * ‖(φ : PairState)‖ ^ 2 →
      OperatorModel.Eigen F E (asFermion S F q W hS φ)

theorem eigen_form_energy (q : ℤ) (W : Chart × Chart → ℝ)
    (F : FermionSystem) (S : MagneticFormSystem) (hS : MagneticFormFacts S F q W)
    (E : ℝ) (ψ : FermionState) (hψ : ψ ∈ F.domain)
    (heig : F.map ⟨ψ, hψ⟩ = E • ψ) :
    let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hψ⟩
    (formPairing S W φ φ).re = E * ‖(φ : PairState)‖ ^ 2 := by
  let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hψ⟩
  have h := hS.operator_form ψ hψ φ
  rw [heig] at h
  change formPairing S W φ φ = inner ℂ (E • (φ : PairState)) (φ : PairState) at h
  change (formPairing S W φ φ).re = _
  rw [h, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow, φ]

theorem rotated_ground_eigen (rayleigh : StandardRayleighEqualityLibrary)
    (q : ℤ) (W : Chart × Chart → ℝ) (R : AngularMomentumAction q)
    (F : FermionSystem) (hF : FermionFacts F q W)
    (S : MagneticFormSystem) (hS : MagneticFormFacts S F q W)
    (A : MagneticRotations q R S F W hS) (hW : RotationInvariantPotential q R W)
    (E : ℝ) (hbottom : ∀ e ∈ OperatorModel.spectrum F, E ≤ e)
    (ψ : FermionState) (hψ : OperatorModel.Eigen F E ψ) (U : MagHK.Spin.Group) :
    OperatorModel.Eigen F E (R.pair U ψ) := by
  obtain ⟨hdom, hne, heig⟩ := hψ
  let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hdom⟩
  have hnorm : ‖(A.lift U φ : PairState)‖ = ‖(φ : PairState)‖ := by
    rw [A.lift_state]
    exact R.pair_norm U (asFermion S F q W hS φ)
  have hnonzero : (A.lift U φ : PairState) ≠ 0 := by
    intro hz
    have hz' : (φ : PairState) = 0 := norm_eq_zero.mp (by rw [← hnorm, hz, norm_zero])
    apply hne
    exact Subtype.ext hz'
  have he : (formPairing S W (A.lift U φ) (A.lift U φ)).re =
      E * ‖(A.lift U φ : PairState)‖ ^ 2 := by
    rw [form_energy_rotation q R S F W hS A hW U φ, hnorm]
    exact eigen_form_energy q W F S hS E ψ hdom heig
  have hv := rayleigh q W F hF S hS E hbottom (A.lift U φ) hnonzero he
  have heq : asFermion S F q W hS (A.lift U φ) = R.pair U ψ := by
    apply Subtype.ext
    exact A.lift_state U φ
  rwa [heq] at hv

theorem ground_singlet (rayleigh : StandardRayleighEqualityLibrary)
    (diagonalize : MagHK.Spin.StandardUnitaryDiagonalization)
    (q : ℤ) (W : Chart × Chart → ℝ) (R : AngularMomentumAction q)
    (F : FermionSystem) (hF : FermionFacts F q W)
    (S : MagneticFormSystem) (hS : MagneticFormFacts S F q W)
    (A : MagneticRotations q R S F W hS) (hW : RotationInvariantPotential q R W)
    (E : ℝ) (hbottom : ∀ e ∈ OperatorModel.spectrum F, E ≤ e)
    (ψ : FermionState) (hψ : OperatorModel.Eigen F E ψ)
    (hsimple : OperatorModel.multiplicity F E = 1) :
    ∀ U, R.pair U ψ = ψ :=
  MagHK.MonopoleSinglet.simple_eigenstate_fixed diagonalize q R F E ψ hψ hsimple
    (rotated_ground_eigen rayleigh q W R F hF S hS A hW E hbottom ψ hψ)

end MagHK.MonopoleRayleigh
