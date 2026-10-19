import MagHK.MonopoleCurrent
import MagHK.MonopoleCoordinates

/-! Gauge cancellation and rotation covariance for the actual physical current. -/
noncomputable section
namespace MagHK.MonopoleCovariance
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleCurrent MagHK.SpinChart
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

abbrev CVector := MagHK.MonopoleQuadrature.Space × MagHK.MonopoleQuadrature.Space

def complexScale (z : ℂ) (v : CVector) : CVector :=
  (z.re • v.1 - z.im • v.2, z.im • v.1 + z.re • v.2)

def rotateVector (R : MagHK.MonopoleQuadrature.Space ≃ₗᵢ[ℝ] MagHK.MonopoleQuadrature.Space) (v : CVector) : CVector := (R v.1, R v.2)

def pointCurrent (z : ℂ) (v : CVector) : MagHK.MonopoleQuadrature.Space := z.re • v.1 + z.im • v.2

def covariantVector (S : MagneticFormSystem) (ψ : S.domain) (i : Fin 2)
    (p : Chart × Chart) : CVector :=
  (∑ k : Fin 3, (S.pi i k ψ p).re • frame k (if i = 0 then p.1 else p.2),
    ∑ k : Fin 3, (S.pi i k ψ p).im • frame k (if i = 0 then p.1 else p.2))

theorem pointCurrent_complexScale (z w : ℂ) (v : CVector) :
    pointCurrent (z * w) (complexScale z v) = Complex.normSq z • pointCurrent w v := by
  simp only [pointCurrent, complexScale, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  module

theorem pointCurrent_rotate (R : MagHK.MonopoleQuadrature.Space ≃ₗᵢ[ℝ] MagHK.MonopoleQuadrature.Space) (z : ℂ) (v : CVector) :
    pointCurrent z (rotateVector R v) = R (pointCurrent z v) := by
  simp [pointCurrent, rotateVector]

theorem pairCurrent_eq (S : MagneticFormSystem) (ψ : S.domain) (p : Chart × Chart) :
    pairCurrent S ψ p = pointCurrent ((ψ : PairState) p) (covariantVector S ψ 0 p) := by
  simp only [pairCurrent, pointCurrent, covariantVector, if_pos rfl, ite_true, Fin.sum_univ_three,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  module

def pairPhase (q : ℤ) (U : MagHK.Spin.Group) (p : Chart × Chart) : ℂ :=
  gaugePhase q U p.1.2 * gaugePhase q U p.2.2

def movedPair (U : MagHK.Spin.Group) (p : Chart × Chart) : Chart × Chart :=
  (movedChart U p.1, movedChart U p.2)

theorem pairPhase_normSq (q : ℤ) (U : MagHK.Spin.Group) (p : Chart × Chart) :
    Complex.normSq (pairPhase q U p) = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [pairPhase, norm_mul, gaugePhase_norm]

def asFermion (S : MagneticFormSystem) (F : FermionSystem) (q : ℤ)
    (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W) (ψ : S.domain) : FermionState :=
  ⟨(ψ : PairState), ((hS.domain_closure _).mp ψ.property).1⟩

/-- Universal closed covariant-derivative transformation law. It describes
all form-domain sections under the literal gauge pullback. It has no current,
Hamiltonian eigenstate, or symmetry conclusion as a field. -/
structure MagneticRotations (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) where
  lift : MagHK.Spin.Group → S.domain → S.domain
  lift_state : ∀ U ψ, (lift U ψ : PairState) =
    (R.pair U (asFermion S F q W hS ψ) : PairState)
  covariant_vector : ∀ U ψ i, ∀ᵐ p ∂pairMeasure,
    covariantVector S (lift U ψ) i p = complexScale (pairPhase q U p)
      (rotateVector (R.rotation U⁻¹).symm (covariantVector S ψ i (movedPair U p)))

def RotationInvariantPotential (q : ℤ) (R : AngularMomentumAction q)
    (W : Chart × Chart → ℝ) : Prop :=
  ∀ U, ∀ᵐ p ∂pairMeasure, W (movedPair U p) = W p

/-- The geometric connection covariance and form-domain closure theorem,
uniform in the integral charge and invariant real scalar interaction. -/
def StandardMagneticActionLibrary : Prop :=
  ∀ q (R : AngularMomentumAction q) (S : MagneticFormSystem) (F : FermionSystem)
    (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W),
    RotationInvariantPotential q R W → Nonempty (MagneticRotations q R S F W hS)

theorem pairCurrent_rotation (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) (A : MagneticRotations q R S F W hS)
    (U : MagHK.Spin.Group) (ψ : S.domain) :
    (fun p => pairCurrent S (A.lift U ψ) p) =ᵐ[pairMeasure]
      fun p => (R.rotation U⁻¹).symm (pairCurrent S ψ (movedPair U p)) := by
  have hw : ∀ᵐ p ∂pairMeasure, (A.lift U ψ : PairState) p =
      pairPhase q U p * (ψ : PairState) (movedPair U p) := by
    rw [A.lift_state]
    exact R.pair_formula U (asFermion S F q W hS ψ)
  filter_upwards [hw, A.covariant_vector U ψ 0] with p hp hv
  rw [pairCurrent_eq, hp, hv, pointCurrent_complexScale, pairPhase_normSq, one_smul,
    pointCurrent_rotate, pairCurrent_eq]

theorem current_rotation (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) (A : MagneticRotations q R S F W hS)
    (U : MagHK.Spin.Group) (ψ : S.domain) :
    (fun x => current S (A.lift U ψ) x) =ᵐ[chartMeasure]
      fun x => (R.rotation U⁻¹).symm (current S ψ (movedChart U x)) := by
  have hp := Measure.ae_ae_of_ae_prod (pairCurrent_rotation q R S F W hS A U ψ)
  have hi := (pairCurrent_integrable S ψ).prod_right_ae
  have him := (R.chart_measure U).quasiMeasurePreserving.ae hi
  filter_upwards [hp, him] with x hx hix
  simp only [current]
  rw [integral_congr_ae hx]
  change (2 : ℝ) • (∫ y, (R.rotation U⁻¹).symm
    (pairCurrent S ψ (movedChart U x, movedChart U y)) ∂chartMeasure) = _
  have hcomm : (∫ y, (R.rotation U⁻¹).symm
      (pairCurrent S ψ (movedChart U x, movedChart U y)) ∂chartMeasure) =
      (R.rotation U⁻¹).symm (∫ y, pairCurrent S ψ
        (movedChart U x, movedChart U y) ∂chartMeasure) :=
    (R.rotation U⁻¹).symm.toLinearIsometry.integral_comp_comm _
  rw [hcomm]
  have hmi : AEStronglyMeasurable (fun y => pairCurrent S ψ (movedChart U x, y))
      (Measure.map (movedChart U) chartMeasure) := by
    rw [(R.chart_measure U).map_eq]
    exact hix.aestronglyMeasurable
  have ht := integral_map (R.chart_measure U).measurable.aemeasurable hmi
  rw [(R.chart_measure U).map_eq] at ht
  rw [← ht, map_smul]

theorem current_fixed_rotation (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) (A : MagneticRotations q R S F W hS)
    (ψ : S.domain)
    (hfixed : ∀ U, R.pair U (asFermion S F q W hS ψ) = asFermion S F q W hS ψ)
    (U : MagHK.Spin.Group) :
    (fun x => current S ψ (movedChart U x)) =ᵐ[chartMeasure]
      fun x => R.rotation U⁻¹ (current S ψ x) := by
  have hlift : A.lift U ψ = ψ := by
    apply Subtype.ext
    rw [A.lift_state, hfixed]
    rfl
  have h := current_rotation q R S F W hS A U ψ
  rw [hlift] at h
  filter_upwards [h] with x hx
  exact ((R.rotation U⁻¹).apply_symm_apply (current S ψ (movedChart U x))).symm.trans
    (congrArg (R.rotation U⁻¹) hx.symm)

end MagHK.MonopoleCovariance
