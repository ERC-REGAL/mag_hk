import MagHK.MonopoleCounterexample
import MagHK.MonopoleDensity
import MagHK.MonopolePatches
import MagHK.MonopoleCartesianDifferential

/-! Paramagnetic currents of the monopole pair in the north gauge.
The ordinary weak momentum is the covariant momentum minus the connection.
All normalized-current assertions are restricted to positive density. -/
noncomputable section
namespace MagHK.MonopoleParamagnetic
open MeasureTheory Filter Set
open MagHK.MonopoleRealization MagHK.MonopoleCurrent MagHK.MonopoleInverse
open MagHK.MonopoleTrial MagHK.MonopoleQuadrature MagHK.MonopoleCoordinates
open scoped ComplexConjugate
set_option maxHeartbeats 1000000
abbrev Space := MagHK.MonopoleQuadrature.Space

def connectionCoefficient (q : ℤ) (x : Chart) : ℝ :=
  ((q : ℝ) / 2) * (1 - x.2.1) / (x.1 * Real.sqrt (1 - x.2.1 ^ 2))
def connection (q : ℤ) (x : Chart) : Space := connectionCoefficient q x • frame 2 x
def component (q : ℤ) (x : Chart) (k : Fin 3) : ℝ :=
  if k = 2 then connectionCoefficient q x else 0
def density (S : MagneticFormSystem) (ψ : S.domain) (x : Chart) : ℝ :=
  2 * ∫ y, Complex.normSq ((ψ : PairState) (x, y)) ∂chartMeasure
def kernel (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain) (p : Chart × Chart) : Space :=
  ∑ k : Fin 3, (conj ((ψ : PairState) p) *
    (S.pi 0 k ψ p - (component q p.1 k : ℂ) * (ψ : PairState) p)).re • frame k p.1
def paramagnetic (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain) (x : Chart) : Space :=
  (2 : ℝ) • ∫ y, kernel q S ψ (x, y) ∂chartMeasure

theorem kernel_eq (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain) (p : Chart × Chart) :
    kernel q S ψ p = pairCurrent S ψ p -
      Complex.normSq ((ψ : PairState) p) • connection q p.1 := by
  have hc (a b : ℂ) (c : ℝ) :
      (conj a * (b - (c : ℂ) * a)).re = (conj a * b).re - Complex.normSq a * c := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.normSq_apply]
    ring
  simp only [kernel, hc, sub_smul, Finset.sum_sub_distrib, pairCurrent]
  congr 1
  simp [Fin.sum_univ_three, component, connection, smul_smul]

theorem current_decomposition (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain) :
    paramagnetic q S ψ =ᵐ[chartMeasure]
      fun x => current S ψ x - density S ψ x • connection q x := by
  have hn : Integrable (fun p => Complex.normSq ((ψ : PairState) p)) pairMeasure := by
    simpa only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ) (ψ : PairState) (ψ : PairState))
  filter_upwards [(pairCurrent_integrable S ψ).prod_right_ae, hn.prod_right_ae] with x hj hn
  simp only [paramagnetic, kernel_eq]
  rw [integral_sub hj (hn.smul_const _), integral_smul_const, smul_sub, smul_smul]
  rfl

theorem zero_current_paramagnetic (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain)
    (hj : current S ψ =ᵐ[chartMeasure] 0) :
    paramagnetic q S ψ =ᵐ[chartMeasure] fun x => -(density S ψ x • connection q x) := by
  filter_upwards [current_decomposition q S ψ, hj] with x hx hzero
  simpa only [hzero, Pi.zero_apply, zero_sub] using hx

theorem normalized_paramagnetic (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain)
    (hj : current S ψ =ᵐ[chartMeasure] 0) :
    ∀ᵐ x ∂chartMeasure, 0 < density S ψ x →
      (density S ψ x)⁻¹ • paramagnetic q S ψ x = -connection q x := by
  filter_upwards [zero_current_paramagnetic q S ψ hj] with x hx
  intro hρ
  rw [hx, smul_neg, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]

theorem connection_neg (q : ℤ) (x : Chart) : connection (-q) x = -connection q x := by
  have hc : connectionCoefficient (-q) x = -connectionCoefficient q x := by
    unfold connectionCoefficient
    push_cast
    ring
  simp only [connection, hc, neg_smul]

theorem connection_ne_zero (q : ℤ) (hq : q ≠ 0) (x : Chart)
    (hr : 0 < x.1) (hμ : x.2.1 ∈ Ioo (-1 : ℝ) 1) : connection q x ≠ 0 := by
  have hs : 0 < Real.sqrt (1 - x.2.1 ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hμ.1, hμ.2])
  have hc : connectionCoefficient q x ≠ 0 := by
    unfold connectionCoefficient
    exact div_ne_zero (mul_ne_zero (div_ne_zero (by exact_mod_cast hq) (by norm_num))
      (by linarith [hμ.2])) (mul_ne_zero hr.ne' hs.ne')
  have hf : frame 2 x ≠ 0 := by
    intro hz
    have hn := frame_norm 2 x ⟨hμ.1.le, hμ.2.le⟩
    rw [hz, norm_zero] at hn
    norm_num at hn
  exact smul_ne_zero hc hf

theorem connection_ne_zero_ae (q : ℤ) (hq : q ≠ 0) :
    ∀ᵐ x ∂chartMeasure, connection q x ≠ 0 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae MagHK.MonopoleExpectation.radialVolume_ae,
    Measure.quasiMeasurePreserving_snd.ae angle_open_ae] with x hr hx
  exact connection_ne_zero q hq x hr hx.1

theorem density_mass (S : MagneticFormSystem) (ψ : S.domain) :
    (∫ x, density S ψ x ∂chartMeasure) = 2 * ‖(ψ : PairState)‖ ^ 2 := by
  have hn : Integrable (fun p => Complex.normSq ((ψ : PairState) p)) pairMeasure := by
    simpa only [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ) (ψ : PairState) (ψ : PairState))
  simp only [density]
  rw [integral_const_mul, ← integral_prod _ hn]
  change 2 * (∫ p, Complex.normSq ((ψ : PairState) p) ∂pairMeasure) = _
  rw [pair_mass]

theorem opposite_paramagnetic_differ (S T : MagneticFormSystem) (ψ : S.domain) (ζ : T.domain)
    (hψ : ‖(ψ : PairState)‖ = 1)
    (hρ : density T ζ =ᵐ[chartMeasure] density S ψ)
    (hj : current S ψ =ᵐ[chartMeasure] 0) (hk : current T ζ =ᵐ[chartMeasure] 0) :
    ¬ paramagnetic 1 S ψ =ᵐ[chartMeasure] paramagnetic (-1) T ζ := by
  intro he
  have hz : density S ψ =ᵐ[chartMeasure] 0 := by
    filter_upwards [he, zero_current_paramagnetic 1 S ψ hj,
      zero_current_paramagnetic (-1) T ζ hk, hρ, connection_ne_zero_ae 1 (by norm_num)]
      with x hx hp hm hρx hA
    rw [hp, hm, hρx, show (-1 : ℤ) = -1 from rfl, connection_neg, smul_neg, neg_neg] at hx
    have hv : (2 * density S ψ x) • connection 1 x = 0 := by
      rw [mul_smul, two_smul]
      exact neg_eq_iff_add_eq_zero.mp hx
    have hr := (smul_eq_zero.mp hv).resolve_right hA
    change density S ψ x = 0
    linarith
  have hi := integral_congr_ae hz
  rw [density_mass, hψ] at hi
  norm_num [Pi.zero_apply] at hi

def coordinates (v : Space) : MagHK.ConstructionData.Space :=
  (((WithLp.ofLp v).2.re, (WithLp.ofLp v).2.im), (WithLp.ofLp v).1)

theorem coordinates_neg (v : Space) : coordinates (-v) = -coordinates v := by
  rfl

theorem coordinates_azimuthal (c : ℝ) (x : Chart) :
    coordinates (c • frame 2 x) = ((-c * Real.sin x.2.2, c * Real.cos x.2.2), 0) := by
  ext <;> simp [coordinates, frame, MagHK.MonopoleGeometry.circle, WithLp.ofLp_smul,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re]

theorem connection_north (q : ℤ) (x : Chart)
    (hx : x ∈ MagHK.MonopoleCartesianDifferential.chartDomain) :
    coordinates (connection q x) =
      MagHK.MonopolePatches.north ((q : ℝ) / 2) (MagHK.MonopoleCartesianDifferential.position x) := by
  rw [MagHK.MonopoleCartesianDifferential.north_as_azimuthal_velocity _ x hx]
  have hs := MagHK.MonopoleCartesianDifferential.root_sq x.2.1 hx.2
  have hsn := (MagHK.MonopoleCartesianDifferential.root_pos x.2.1 hx.2).ne'
  have hr := hx.1.ne'
  have hm : 1 - x.2.1 ^ 2 ≠ 0 := by nlinarith [hx.2.1, hx.2.2]
  change coordinates (connectionCoefficient q x • frame 2 x) = _
  rw [coordinates_azimuthal]
  dsimp [MagHK.MonopoleCartesianDifferential.root] at hs hsn
  ext <;> simp [connectionCoefficient, MagHK.MonopoleCartesianDifferential.velocity,
    MagHK.MonopoleCartesianDifferential.root, smul_eq_mul] <;>
    field_simp [hr, hm, show Real.sqrt (1 - x.2.1 ^ 2) ≠ 0 from hsn] <;>
    simp only [hs] <;> ring

theorem normalized_north (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain)
    (hj : current S ψ =ᵐ[chartMeasure] 0) :
    ∀ᵐ x ∂chartMeasure, 0 < density S ψ x →
      coordinates ((density S ψ x)⁻¹ • paramagnetic q S ψ x) =
        -MagHK.MonopolePatches.north ((q : ℝ) / 2)
          (MagHK.MonopoleCartesianDifferential.position x) := by
  filter_upwards [normalized_paramagnetic q S ψ hj,
    Measure.quasiMeasurePreserving_fst.ae MagHK.MonopoleExpectation.radialVolume_ae,
    Measure.quasiMeasurePreserving_snd.ae angle_open_ae] with x hn hr hx
  intro hρ
  rw [hn hρ, coordinates_neg, connection_north q x ⟨hr, hx.1⟩]

/-- The smooth representative of the normalized paramagnetic current has
curl minus the magnetic field, on the north patch. -/
theorem normalized_north_curl (g : ℝ) (p : MagHK.ConstructionData.Space)
    (hp : p ∈ MagHK.MonopolePatches.northDomain) :
    MagHK.MonopolePatches.curl (-MagHK.MonopolePatches.north g) p =
      -MagHK.MonopolePatches.field g p := by
  have hn : MagHK.MonopolePatches.curl (-MagHK.MonopolePatches.north g) p =
      -MagHK.MonopolePatches.curl (MagHK.MonopolePatches.north g) p := by
    ext <;> simp [MagHK.MonopolePatches.curl, deriv.fun_neg] <;> ring
  rw [hn, MagHK.MonopolePatches.north_curl g p hp]

theorem normalized_north_curl_ne_zero (g : ℝ) (hg : g ≠ 0)
    (p : MagHK.ConstructionData.Space) (hp : p ∈ MagHK.MonopolePatches.northDomain) :
    MagHK.MonopolePatches.curl (-MagHK.MonopolePatches.north g) p ≠ 0 := by
  rw [normalized_north_curl g p hp]
  apply neg_ne_zero.mpr
  exact smul_ne_zero (div_ne_zero hg (pow_ne_zero _
    (MagHK.MonopolePatches.radius_pos p (MagHK.MonopolePatches.north_nonzero hp)).ne'))
    (MagHK.MonopolePatches.north_nonzero hp)

theorem chart_zero_of_physical (S : MagneticFormSystem) (ψ : S.domain)
    (hj : physicalCurrent S ψ =ᵐ[volume] 0) : current S ψ =ᵐ[chartMeasure] 0 := by
  filter_upwards [physicalCurrent_chart S ψ, point_measurePreserving.quasiMeasurePreserving.ae hj]
    with x hx hz
  exact hx.symm.trans hz

theorem pair_paramagnetic_differ (P : MagHK.MonopoleCounterexample.Pair) :
    ¬ paramagnetic 1 P.plus_form P.plus_form_state =ᵐ[chartMeasure]
      paramagnetic (-1) P.minus_form P.minus_form_state := by
  apply opposite_paramagnetic_differ P.plus_form P.minus_form P.plus_form_state P.minus_form_state
  · simpa only [P.plus_represented, Submodule.norm_coe] using P.plus_norm
  · have he := point_measurePreserving.quasiMeasurePreserving.ae P.density_eq
    filter_upwards [he, physicalDensity_chart P.positive, physicalDensity_chart P.negative]
      with x hx hp hm
    change density P.minus_form P.minus_form_state x = density P.plus_form P.plus_form_state x
    unfold density
    rw [P.minus_represented, P.plus_represented]
    exact hm.symm.trans (hx.trans hp)
  · exact chart_zero_of_physical _ _ P.plus_zero_current
  · exact chart_zero_of_physical _ _ P.minus_zero_current

theorem pair_normalized_paramagnetic (P : MagHK.MonopoleCounterexample.Pair) :
    (∀ᵐ x ∂chartMeasure, 0 < density P.plus_form P.plus_form_state x →
      coordinates ((density P.plus_form P.plus_form_state x)⁻¹ •
        paramagnetic 1 P.plus_form P.plus_form_state x) =
          -MagHK.MonopolePatches.north (1 / 2) (MagHK.MonopoleCartesianDifferential.position x)) ∧
    (∀ᵐ x ∂chartMeasure, 0 < density P.minus_form P.minus_form_state x →
      coordinates ((density P.minus_form P.minus_form_state x)⁻¹ •
        paramagnetic (-1) P.minus_form P.minus_form_state x) =
          -MagHK.MonopolePatches.north (-1 / 2) (MagHK.MonopoleCartesianDifferential.position x)) := by
  constructor
  · simpa using normalized_north 1 P.plus_form P.plus_form_state
      (chart_zero_of_physical _ _ P.plus_zero_current)
  · simpa using normalized_north (-1) P.minus_form P.minus_form_state
      (chart_zero_of_physical _ _ P.minus_zero_current)

/-- Euclidean representative obtained from the actual inverse chart. -/
def physicalParamagnetic (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain) (z : Space) : Space :=
  paramagnetic q S ψ (inverse z)

theorem physicalParamagnetic_chart (q : ℤ) (S : MagneticFormSystem) (ψ : S.domain) :
    (fun x => physicalParamagnetic q S ψ (MagHK.SpinChart.point x)) =ᵐ[chartMeasure]
      paramagnetic q S ψ := by
  filter_upwards [inverse_point_ae] with x hx
  simp only [physicalParamagnetic, hx, id_eq]

theorem pair_physical_paramagnetic_differ (P : MagHK.MonopoleCounterexample.Pair) :
    ¬ physicalParamagnetic 1 P.plus_form P.plus_form_state =ᵐ[volume]
      physicalParamagnetic (-1) P.minus_form P.minus_form_state := by
  intro he
  apply pair_paramagnetic_differ P
  filter_upwards [point_measurePreserving.quasiMeasurePreserving.ae he,
    physicalParamagnetic_chart 1 P.plus_form P.plus_form_state,
    physicalParamagnetic_chart (-1) P.minus_form P.minus_form_state] with x hx hp hm
  exact hp.symm.trans (hx.trans hm)

end MagHK.MonopoleParamagnetic
