import MagHK.MonopoleCartesianDifferential
import MagHK.CoordinateMagnetic
import MagHK.MonopoleDifferential

/-! The literal Cartesian covariant operator agrees with the spherical
operator used for the monopole Friedrichs realization. -/
noncomputable section
namespace MagHK.MonopoleCartesianOperator
open Set Filter MagHK.ConstructionData MagHK.MonopolePatches MagHK.MonopolePatchGauge
open MagHK.MonopoleRealization MagHK.MonopoleCartesianDifferential
open scoped ContDiff Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

abbrev Chart := MagHK.MonopoleRealization.Chart

def basis : Fin 3 → Space := ![((1, 0), 0), ((0, 1), 0), ((0, 0), 1)]

theorem basis_decomposition (p : Space) : p = ∑ j : Fin 3, component p j • basis j := by
  ext <;> simp [Fin.sum_univ_three, component, basis, smul_eq_mul]

theorem metric_contraction (x : Chart) (hx : x ∈ chartDomain)
    (B : Space →L[ℝ] Space →L[ℝ] ℂ) :
    (∑ i : Fin 3, weight x i • B (velocity x i) (velocity x i)) =
      ∑ j : Fin 3, B (basis j) (basis j) :=
  MagHK.CoordinateLaplacian.bilinear_contraction basis component basis_decomposition
    (velocity x) (weight x) (metric_identity x hx) B

theorem cartesian_laplacian_pullback (F : Space → ℂ) (x : Chart)
    (hx : x ∈ chartDomain) (hF : ContDiffAt ℝ 2 F (position x)) :
    MagHK.CoordinateLaplacian.laplacian basis F (position x) =
      Dr (Dr (F ∘ position)) x + (2 / x.1 : ℝ) * Dr (F ∘ position) x +
      ((1 - x.2.1 ^ 2) / x.1 ^ 2 : ℝ) * Dmu (Dmu (F ∘ position)) x +
      (-2 * x.2.1 / x.1 ^ 2 : ℝ) * Dmu (F ∘ position) x +
      (1 / (x.1 ^ 2 * (1 - x.2.1 ^ 2)) : ℝ) * Dphi (Dphi (F ∘ position)) x := by
  have hv (i : Fin 3) : deriv (fun t => position (replace i x t)) (coord x i) = velocity x i :=
    (position_hasDerivAt i x hx).deriv
  have ha (i : Fin 3) := curve_second_derivative i x hx
  have h := MagHK.CoordinateLaplacian.laplacian_from_curves basis F (position x)
    (fun i t => position (replace i x t)) (coord x) (weight x) (drift x)
    (by intro i; rw [replace_self]) hF (fun i => curve_contDiffAt i x hx)
    (by intro B; simpa only [hv] using metric_contraction x hx B)
    (by simpa only [hv, ha] using drift_identity x hx)
  rw [h]
  simp [Fin.sum_univ_three, weight, drift, coord, replace, Dr, Dmu, Dphi,
    MagHK.MonopoleAngular.Dμ, MagHK.MonopoleAngular.Dφ, Function.comp_def, Complex.real_smul]
  ring

def northComponents (g : ℝ) (i : Fin 3) (p : Space) : ℝ := component (north g p) i

theorem north_contDiffAt (g : ℝ) (p : Space) (hp : p ∈ northDomain) :
    ContDiffAt ℝ ∞ (north g) p := by
  have hopen : IsOpen northDomain := by
    apply isOpen_lt continuous_const
    change Continuous (fun p : Space => MagHK.DiracString.radius p + p.2)
    unfold MagHK.DiracString.radius
    fun_prop
  exact (north_smooth g p hp).contDiffAt (hopen.mem_nhds hp)

theorem northComponents_differentiable (g : ℝ) (p : Space) (hp : p ∈ northDomain)
    (i : Fin 3) : DifferentiableAt ℝ (northComponents g i) p := by
  have h := (north_contDiffAt g p hp).differentiableAt (by simp)
  fin_cases i
  · exact h.fst.fst
  · exact h.fst.snd
  · exact h.snd

def cartesianReplace (i : Fin 3) (p : Space) (t : ℝ) : Space :=
  ![((t, p.1.2), p.2), ((p.1.1, t), p.2), (p.1, t)] i

theorem cartesianReplace_eq (i : Fin 3) (p : Space) (t : ℝ) :
    cartesianReplace i p t = p + (t - component p i) • basis i := by
  fin_cases i <;> ext <;> simp [cartesianReplace, component, basis, smul_eq_mul]

theorem cartesian_directional (G : Space → ℝ) (p : Space)
    (hG : DifferentiableAt ℝ G p) (i : Fin 3) :
    fderiv ℝ G p (basis i) = deriv (fun t => G (cartesianReplace i p t)) (component p i) := by
  have hc := ((((hasDerivAt_id (component p i)).sub_const (component p i)).smul_const
    (basis i)).const_add p)
  have hc' : HasDerivAt (fun t => cartesianReplace i p t) (basis i) (component p i) := by
    simpa only [cartesianReplace_eq, id_eq, one_smul] using hc
  have he : cartesianReplace i p (component p i) = p := by
    rw [cartesianReplace_eq, sub_self, zero_smul, add_zero]
  have hG' : HasFDerivAt G (fderiv ℝ G p) (cartesianReplace i p (component p i)) := by
    simpa only [he] using hG.hasFDerivAt
  exact (hG'.comp_hasDerivAt (component p i) hc').deriv.symm

theorem north_divergence_trace (g : ℝ) (p : Space) (hp : p ∈ northDomain) :
    ∑ i : Fin 3, fderiv ℝ (northComponents g i) p (basis i) = 0 := by
  have he (i : Fin 3) := cartesian_directional (northComponents g i) p
    (northComponents_differentiable g p hp i) i
  simp_rw [he]
  simpa [Fin.sum_univ_three, northComponents, component, cartesianReplace, divergence]
    using north_divergence g p hp

theorem north_component_coupling (g : ℝ) (F : Space → ℂ) (x : Chart)
    (hx : x ∈ chartDomain) (hF : DifferentiableAt ℝ F (position x)) :
    (∑ i : Fin 3, (northComponents g i (position x) : ℂ) *
      MagHK.CoordinateMagnetic.directional basis F i (position x)) =
      (g * (1 - x.2.1) / (x.1 ^ 2 * (1 - x.2.1 ^ 2)) : ℝ) * Dphi (F ∘ position) x := by
  have he := congrArg (fderiv ℝ F (position x)) (basis_decomposition (north g (position x)))
  simp only [map_sum, map_smul] at he
  simp_rw [← Complex.real_smul]
  change (∑ i : Fin 3, component (north g (position x)) i •
    fderiv ℝ F (position x) (basis i)) = _
  rw [← he]
  exact north_directional_derivative g F x hx hF

theorem north_component_norm (g : ℝ) (x : Chart) (hx : x ∈ chartDomain) :
    (∑ i : Fin 3, (northComponents g i (position x) : ℂ) ^ 2) =
      ((g * (1 - x.2.1)) ^ 2 / (x.1 ^ 2 * (1 - x.2.1 ^ 2)) : ℝ) := by
  have h := congrArg Complex.ofReal (north_norm_sq g x hx)
  simpa [Fin.sum_univ_three, northComponents, component, dot_apply, pow_two] using h

/-- Literal squared Cartesian covariant derivatives pull back to the
spherical expression whose Friedrichs form defines the monopole oscillator. -/
theorem north_magnetic_square_pullback (q : ℤ) (F : Space → ℂ) (x : Chart)
    (hx : x ∈ chartDomain) (hF : ContDiffAt ℝ 2 F (position x)) :
    MagHK.CoordinateMagnetic.magneticSquare basis (northComponents ((q : ℝ) / 2)) F
      (position x) = oneExpression q (F ∘ position) x - (x.1 ^ 2 : ℝ) * F (position x) := by
  have hp : position x ∈ northDomain :=
    (north_domain_iff _).mpr (Or.inl (position_off_axis x hx))
  rw [MagHK.CoordinateMagnetic.magnetic_square_expansion basis
    (northComponents ((q : ℝ) / 2)) F (position x) hF
    (fun i => northComponents_differentiable _ _ hp i),
    cartesian_laplacian_pullback F x hx hF,
    north_component_coupling _ F x hx (hF.differentiableAt (by norm_num)),
    north_component_norm _ x hx]
  have hdiv : (∑ i : Fin 3, (fderiv ℝ (northComponents ((q : ℝ) / 2) i)
      (position x) (basis i) : ℂ)) = 0 := by
    exact_mod_cast north_divergence_trace ((q : ℝ) / 2) (position x) hp
  rw [hdiv]
  have hr : (x.1 : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  have hm : (1 - (x.2.1 : ℂ) ^ 2) ≠ 0 := by
    have hh : 1 - x.2.1 ^ 2 ≠ 0 := by nlinarith [hx.2.1, hx.2.2]
    exact_mod_cast hh
  unfold oneExpression MagHK.MonopoleAngular.angularExpression Dmu Dphi
  simp only [Function.comp_apply]
  push_cast
  field_simp [hr, hm]
  ring

def xyzIndex : Fin 3 → Fin 3 := ![2, 0, 1]
def chartPartial (f : Chart → ℂ) (i : Fin 3) (x : Chart) : ℂ :=
  deriv (fun t => f (replace i x t)) (coord x i)

theorem inverse_frame (x : Chart) (hx : x ∈ chartDomain) (j : Fin 3) :
    basis j = ∑ i : Fin 3, (weight x i * component (velocity x i) j) • velocity x i := by
  have hc (k : Fin 3) : component (basis j) k =
      component (∑ i : Fin 3, (weight x i * component (velocity x i) j) • velocity x i) k := by
    have hm := (metric_identity x hx j k).symm
    fin_cases k <;> fin_cases j <;>
      simpa [component, basis, Fin.sum_univ_three, smul_eq_mul] using hm
  exact Prod.ext (Prod.ext (hc 0) (hc 1)) (hc 2)

theorem chartPartial_pullback (F : Space → ℂ) (x : Chart) (hx : x ∈ chartDomain)
    (hF : DifferentiableAt ℝ F (position x)) (i : Fin 3) :
    chartPartial (F ∘ position) i x = fderiv ℝ F (position x) (velocity x i) := by
  have hF' : HasFDerivAt F (fderiv ℝ F (position x)) (position (replace i x (coord x i))) := by
    rw [replace_self]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (coord x i) (position_hasDerivAt i x hx)).deriv

theorem directional_pullback (F : Space → ℂ) (x : Chart) (hx : x ∈ chartDomain)
    (hF : DifferentiableAt ℝ F (position x)) (j : Fin 3) :
    MagHK.CoordinateMagnetic.directional basis F j (position x) =
      ∑ i : Fin 3, (weight x i * component (velocity x i) j) • chartPartial (F ∘ position) i x := by
  have h := congrArg (fderiv ℝ F (position x)) (inverse_frame x hx j)
  simp only [map_sum, map_smul] at h
  simp_rw [chartPartial_pullback F x hx hF]
  exact h

/-- Cartesian momentum components are the closed-frame derivatives, with
only the explicit coordinate permutation from x,y,z to z,x,y. -/
theorem north_momentum_pullback (q : ℤ) (F : Space → ℂ) (x : Chart)
    (hx : x ∈ chartDomain) (hF : DifferentiableAt ℝ F (position x)) (k : Fin 3) :
    MagHK.CoordinateMagnetic.momentum basis (northComponents ((q : ℝ) / 2)) F
      (xyzIndex k) (position x) =
      MagHK.MonopoleDifferential.momentumVector q (F ∘ position) x k := by
  unfold MagHK.CoordinateMagnetic.momentum
  rw [directional_pullback F x hx hF]
  simp only [northComponents, north_as_azimuthal_velocity _ x hx]
  have hr : (x.1 : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  have hs : (root x.2.1 : ℂ) ≠ 0 := by exact_mod_cast (root_pos x.2.1 hx.2).ne'
  have hsq : (root x.2.1 : ℂ) ^ 2 = 1 - (x.2.1 : ℂ) ^ 2 := by
    exact_mod_cast root_sq x.2.1 hx.2
  have hm : (1 - (x.2.1 : ℂ) ^ 2) ≠ 0 := by rw [← hsq]; exact pow_ne_zero _ hs
  have hsine : MagHK.MonopoleDifferential.sine x.2.1 = root x.2.1 := rfl
  have hsroot : Real.sqrt (1 - x.2.1 ^ 2) = root x.2.1 := rfl
  fin_cases k <;>
    norm_num [xyzIndex, Fin.sum_univ_three, weight, velocity, component, smul_eq_mul,
      chartPartial, replace, coord, MagHK.MonopoleDifferential.momentumVector,
      MagHK.MonopoleDifferential.radialVector, MagHK.MonopoleDifferential.polarVector,
      MagHK.MonopoleDifferential.azimuthVector, hsine, hsroot, frameDerivative,
      magneticPhi, northCoefficient, Dr, Dmu, Dphi, MagHK.MonopoleAngular.Dμ,
      MagHK.MonopoleAngular.Dφ, Function.comp_def, Complex.real_smul]
  all_goals push_cast
  all_goals field_simp [hr, hs, hm]
  all_goals try ring_nf
  all_goals try simp only [hsq]
  all_goals ring

theorem positionVector_eq (x : Chart) (k : Fin 3) :
    (component (position x) (xyzIndex k) : ℂ) =
      MagHK.MonopoleDifferential.positionVector x k := by
  have hsine : MagHK.MonopoleDifferential.sine x.2.1 = root x.2.1 := rfl
  fin_cases k <;>
    norm_num [component, position, xyzIndex, MagHK.MonopoleDifferential.positionVector,
      MagHK.MonopoleDifferential.radialVector, hsine]
  all_goals push_cast
  all_goals ring

/-- The displayed r × π + g r̂ is the angular-momentum differential
operator for the actual Cartesian north potential. -/
theorem north_angular_momentum_pullback (q : ℤ) (F : Space → ℂ) (x : Chart)
    (hx : x ∈ chartDomain) (hF : DifferentiableAt ℝ F (position x)) (k : Fin 3) :
    MagHK.MonopoleDifferential.cross
      (fun j => (component (position x) (xyzIndex j) : ℂ))
      (fun j => MagHK.CoordinateMagnetic.momentum basis (northComponents ((q : ℝ) / 2))
        F (xyzIndex j) (position x)) k +
      ((q : ℝ) / 2 : ℝ) * MagHK.MonopoleDifferential.radialVector x.2 k * F (position x) =
      MagHK.MonopoleDifferential.angularMomentum ((q : ℝ) / 2) k
        (fun p => (F ∘ position) (x.1, p)) x.2 := by
  simp_rw [positionVector_eq, north_momentum_pullback q F x hx hF]
  exact MagHK.MonopoleDifferential.angularFromMomentum_eq q (F ∘ position) x hx.1.ne' hx.2 k


theorem twiceDifferentiable_of_contDiffAt (Y : MagHK.MonopoleTrial.Angle → ℂ)
    (p : MagHK.MonopoleTrial.Angle) (hY : ContDiffAt ℝ 2 Y p) :
    MagHK.MonopoleDifferential.TwiceDifferentiable Y p := by
  have hm : MagHK.MonopoleAngular.Dμ Y =ᶠ[nhds p] (fun z => fderiv ℝ Y z (1, 0)) := by
    filter_upwards [hY.eventually (by norm_num)] with z hz
    exact MagHK.MonopoleDifferential.Dmu_eq_fderiv Y z (hz.differentiableAt (by norm_num))
  have hp : MagHK.MonopoleAngular.Dφ Y =ᶠ[nhds p] (fun z => fderiv ℝ Y z (0, 1)) := by
    filter_upwards [hY.eventually (by norm_num)] with z hz
    exact MagHK.MonopoleDifferential.Dphi_eq_fderiv Y z (hz.differentiableAt (by norm_num))
  refine ⟨hY.differentiableAt (by norm_num), ?_, ?_⟩
  · exact (((hY.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)).congr_of_eventuallyEq hm
  · exact (((hY.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)).congr_of_eventuallyEq hp

/-- The radial r⁻²(L_g²−g²) splitting for the actual Cartesian operator. -/
theorem north_magnetic_casimir_split (q : ℤ) (F : Space → ℂ) (x : Chart)
    (hx : x ∈ chartDomain) (hF : ContDiffAt ℝ 2 F (position x)) :
    MagHK.CoordinateMagnetic.magneticSquare basis (northComponents ((q : ℝ) / 2)) F
      (position x) =
      -Dr (Dr (F ∘ position)) x - (2 / x.1 : ℝ) * Dr (F ∘ position) x +
      (MagHK.MonopoleDifferential.angularSquare ((q : ℝ) / 2)
          (fun p => (F ∘ position) (x.1, p)) x.2 -
        (((q : ℝ) / 2) ^ 2 : ℝ) * F (position x)) / (x.1 ^ 2 : ℝ) := by
  have hc : ContDiffAt ℝ 2 (F ∘ position) x :=
    hF.comp x ((position_contDiffAt x hx).of_le (by simp))
  have hang : ContDiffAt ℝ 2 (fun p => (F ∘ position) (x.1, p)) x.2 :=
    ContDiffAt.comp (f := fun p : MagHK.MonopoleTrial.Angle => (x.1, p))
      (g := F ∘ position) x.2 hc (by fun_prop)
  rw [north_magnetic_square_pullback q F x hx hF,
    MagHK.MonopoleDifferential.radial_splitting q (F ∘ position) x hx.2
      (twiceDifferentiable_of_contDiffAt _ _ hang)]
  simp only [Function.comp_apply]
  ring

end MagHK.MonopoleCartesianOperator
