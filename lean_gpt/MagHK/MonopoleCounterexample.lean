import MagHK.MonopolePositive
import MagHK.MonopoleInverse
import MagHK.MonopoleFlux
import MagHK.MonopoleCurrentConclusion
import MagHK.WeakGauge

/-! The two physical monopole charges share their normalized ground-state
density and have zero physical current. Their actual Friedrichs operators
have simple isolated correlated ground states, and the connections cannot
be related by a smooth gauge. -/
noncomputable section
namespace MagHK.MonopoleCounterexample
open MeasureTheory
open MagHK.MonopoleRealization MagHK.MonopoleTimeReversal MagHK.MonopoleInverse

structure Pair where
  plus : FermionSystem
  minus : FermionSystem
  energy : ℝ
  positive : FermionState
  negative : FermionState
  time_reversal : negative = conjugation positive
  plus_facts : FermionFacts plus 1 coulomb
  minus_facts : FermionFacts minus (-1) coulomb
  plus_eigen : OperatorModel.Eigen plus energy positive
  minus_eigen : OperatorModel.Eigen minus energy negative
  plus_norm : ‖positive‖ = 1
  minus_norm : ‖negative‖ = 1
  plus_ground : GroundState plus energy (fun p => (positive : PairState) p)
  minus_ground : GroundState minus energy (fun p => (negative : PairState) p)
  plus_gap : SpectralGap plus energy (MagHK.Monopole.freeGap - MagHK.Monopole.coulombBound)
  minus_gap : SpectralGap minus energy (MagHK.Monopole.freeGap - MagHK.Monopole.coulombBound)
  plus_correlated : ¬ IsSlater positive
  minus_correlated : ¬ IsSlater negative
  plus_form : MagneticFormSystem
  minus_form : MagneticFormSystem
  plus_form_state : plus_form.domain
  minus_form_state : minus_form.domain
  plus_form_facts : MagneticFormFacts plus_form plus 1 coulomb
  minus_form_facts : MagneticFormFacts minus_form minus (-1) coulomb
  plus_represented : (plus_form_state : PairState) = (positive : PairState)
  minus_represented : (minus_form_state : PairState) = (negative : PairState)
  density_eq : physicalDensity negative =ᵐ[volume] physicalDensity positive
  plus_zero_current : physicalCurrent plus_form plus_form_state =ᵐ[volume] 0
  minus_zero_current : physicalCurrent minus_form minus_form_state =ᵐ[volume] 0
  not_gauge : ¬ MagHK.MonopoleFlux.LocallyGaugeEquivalent 1 (-1)

theorem of_positive_with_state (spectral : StandardAntiunitaryLibrary)
    (friedrichs : StandardFriedrichsConjugationLibrary) (G : MagHK.MonopolePositive.Ground)
    (u : G.form.domain) (hu : (u : PairState) = (G.state : PairState))
    (hj : MagHK.MonopoleCurrent.current G.form u =ᵐ[chartMeasure] 0) :
    ∃ P : Pair, P.positive = G.state := by
  obtain ⟨hF, he, hn, hg, hgap, hns, _, S', ζ, hS', hζ, hj'⟩ :=
    opposite_charge_of_ground spectral friedrichs 1 coulomb G.operator G.energy
      (MagHK.Monopole.freeGap - MagHK.Monopole.coulombBound) G.state G.form u
      G.facts G.form_facts hu G.eigen G.norm_one G.ground G.gap G.not_slater hj
  exact ⟨{
    plus := G.operator
    minus := reverseOperator G.operator
    energy := G.energy
    positive := G.state
    negative := conjugation G.state
    time_reversal := rfl
    plus_facts := G.facts
    minus_facts := hF
    plus_eigen := G.eigen
    minus_eigen := he
    plus_norm := G.norm_one
    minus_norm := hn
    plus_ground := G.ground
    minus_ground := hg
    plus_gap := G.gap
    minus_gap := hgap
    plus_correlated := G.not_slater
    minus_correlated := hns
    plus_form := G.form
    minus_form := S'
    plus_form_state := u
    minus_form_state := ζ
    plus_form_facts := G.form_facts
    minus_form_facts := hS'
    plus_represented := hu
    minus_represented := hζ
    density_eq := physicalDensity_conjugate G.state
    plus_zero_current := physicalCurrent_zero G.form u hj
    minus_zero_current := physicalCurrent_zero S' ζ hj'
    not_gauge := MagHK.MonopoleFlux.opposite_charges_not_gauge }, rfl⟩

theorem of_positive (spectral : StandardAntiunitaryLibrary)
    (friedrichs : StandardFriedrichsConjugationLibrary) (G : MagHK.MonopolePositive.Ground)
    (u : G.form.domain) (hu : (u : PairState) = (G.state : PairState))
    (hj : MagHK.MonopoleCurrent.current G.form u =ᵐ[chartMeasure] 0) : Nonempty Pair := by
  obtain ⟨P, _⟩ := of_positive_with_state spectral friedrichs G u hu hj
  exact ⟨P⟩

theorem Pair.physical_norms (P : Pair) :
    (∫ p : MagHK.SpinChart.Space × MagHK.SpinChart.Space,
      Complex.normSq (physicalWave P.positive p) ∂volume.prod volume) = 1 ∧
    (∫ p : MagHK.SpinChart.Space × MagHK.SpinChart.Space,
      Complex.normSq (physicalWave P.negative p) ∂volume.prod volume) = 1 := by
  simp only [physicalWave_mass, P.plus_norm, P.minus_norm, one_pow, and_self]

theorem Pair.density_masses (P : Pair) :
    (∫ z : MagHK.SpinChart.Space, physicalDensity P.positive z) = 2 ∧
    (∫ z : MagHK.SpinChart.Space, physicalDensity P.negative z) = 2 := by
  simp only [physicalDensity_mass, P.plus_norm, P.minus_norm, one_pow, mul_one, and_self]

theorem Pair.numeric_gaps (P : Pair) :
    (∀ e ∈ OperatorModel.spectrum P.plus, e ≠ P.energy → P.energy + (533 / 500 : ℝ) < e) ∧
    (∀ e ∈ OperatorModel.spectrum P.minus, e ≠ P.energy → P.energy + (533 / 500 : ℝ) < e) := by
  constructor
  · intro e he hne
    have hg := P.plus_gap e he hne
    have hn := MagHK.Monopole.explicit_gap_lower_bound
    linarith
  · intro e he hne
    have hg := P.minus_gap e he hne
    have hn := MagHK.Monopole.explicit_gap_lower_bound
    linarith

theorem Pair.not_weak_gauge (_P : Pair)
    (regularity : MagHK.WeakGauge.StandardGradientRegularityLibrary) :
    ¬ MagHK.WeakGauge.LocallyGaugeEquivalent 1 (-1) :=
  MagHK.WeakGauge.opposite_monopoles_not_weak_gauge regularity

/-- The complete interacting pair, conditional only on the uniform background
operator, angular-momentum and regularity results explicitly listed here. -/
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
    (averaging : MagHK.MonopoleCurrentAveraging.StandardRotationFixedSpaceLibrary) :
    Nonempty Pair := by
  obtain ⟨G⟩ := MagHK.MonopolePositive.exists_ground monopole exterior hardy minmax angular
    magnetic rayleigh diagonalize isotypic domains tensor
  obtain ⟨u, hu, hj⟩ := MagHK.MonopoleCurrentConclusion.current_zero weak averaging
    1 G.action G.form G.operator G.facts G.form_facts G.rotations G.energy G.state
    G.eigen G.norm_one G.fixed
  exact of_positive spectral friedrichs G u hu hj

end MagHK.MonopoleCounterexample
