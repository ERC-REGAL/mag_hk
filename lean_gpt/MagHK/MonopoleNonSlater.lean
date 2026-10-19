import MagHK.MonopoleOccupied
import MagHK.DoubletDeterminant
import MagHK.MonopoleCorrelation

/-! The singlet-to-correlation argument on actual section L². Occupied-space
invariance, the rank-two deduction, the determinant factorization, and the
contradiction with the actual Coulomb eigen-equation are all composed here. -/
noncomputable section
namespace MagHK.MonopoleSeparation
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.SpinChart MagHK.MonopoleMultiplet
open MagHK.MonopoleTensorDomain MagHK.MonopoleOccupied

theorem singlet_not_slater
    (isotypic : StandardIsotypicLibrary)
    (domains : StandardCoulombOperatorLibrary) (tensor : StandardSeparatedDomainLibrary)
    (R : AngularMomentumAction 1) (F₀ F : FermionSystem)
    (hF₀ : FermionFacts F₀ 1 0) (hF : FermionFacts F 1 coulomb)
    (E : ℝ) (ψ : FermionState) (hψ : OperatorModel.Eigen F E ψ)
    (hsinglet : ∀ U, R.pair U ψ = ψ) : ¬ IsSlater ψ := by
  rintro ⟨a, b, hab, hrep⟩
  obtain ⟨hfinite, hdim, hinv⟩ := occupied_invariant R ψ a b hab hrep hsinglet
  obtain ⟨Y, hY⟩ := isotypic 1 R
  obtain ⟨M⟩ := hY (Submodule.span ℂ {a, b}) hfinite hinv
  obtain ⟨f, u, v, hn, hu, hv, hK⟩ := common_radial_doublet Y _ M hdim
  have ha : a ∈ Submodule.span ℂ {u, v} := by
    rw [← hK]
    exact Submodule.subset_span (by simp)
  have hb : b ∈ Submodule.span ℂ {u, v} := by
    rw [← hK]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := determinant_of_common_radial f u v a b hu hv ha hb
  have hsep : ∀ᵐ p ∂pairMeasure, (ψ : PairState) p = c * separatedWave f p := by
    filter_upwards [hrep, hc] with p hp hq
    exact hp.trans hq
  exact no_separated_eigenstate domains tensor F₀ F hF₀ hF E ψ hψ f c
    (coefficient_nonzero ψ hψ.choose_spec.1 f c hsep) hn hsep

end MagHK.MonopoleSeparation
