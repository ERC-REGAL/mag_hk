import MagHK.MonopolePatchGauge
import MagHK.MonopoleRealization
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Cartesian spherical-coordinate jets and the north connection pullback.
The radius, polar cosine and azimuth are literal functions. All geometric
identities in this module are proved from their displayed formulas. -/
noncomputable section
namespace MagHK.MonopoleCartesianDifferential
open Set Filter MagHK.ConstructionData MagHK.MonopolePatches MagHK.MonopolePatchGauge
open MagHK.MonopoleRealization
open scoped ContDiff Topology
set_option maxHeartbeats 1000000

abbrev Chart := MagHK.MonopoleRealization.Chart

def chartDomain : Set Chart := {x | 0 < x.1 ∧ x.2.1 ∈ Ioo (-1) 1}
def root (μ : ℝ) : ℝ := Real.sqrt (1 - μ ^ 2)
def position (x : Chart) : Space :=
  ((x.1 * root x.2.1 * Real.cos x.2.2, x.1 * root x.2.1 * Real.sin x.2.2),
    x.1 * x.2.1)
def coord (x : Chart) : Fin 3 → ℝ := ![x.1, x.2.1, x.2.2]
def component (p : Space) : Fin 3 → ℝ := ![p.1.1, p.1.2, p.2]
def replace (i : Fin 3) (x : Chart) (t : ℝ) : Chart :=
  ![(t, x.2), (x.1, t, x.2.2), (x.1, x.2.1, t)] i

def velocity (x : Chart) : Fin 3 → Space :=
  ![((root x.2.1 * Real.cos x.2.2, root x.2.1 * Real.sin x.2.2), x.2.1),
    ((-x.1 * x.2.1 / root x.2.1 * Real.cos x.2.2,
      -x.1 * x.2.1 / root x.2.1 * Real.sin x.2.2), x.1),
    ((-x.1 * root x.2.1 * Real.sin x.2.2,
      x.1 * root x.2.1 * Real.cos x.2.2), 0)]
def acceleration (x : Chart) : Fin 3 → Space :=
  ![0, ((-x.1 / root x.2.1 ^ 3 * Real.cos x.2.2,
    -x.1 / root x.2.1 ^ 3 * Real.sin x.2.2), 0),
    ((-x.1 * root x.2.1 * Real.cos x.2.2,
      -x.1 * root x.2.1 * Real.sin x.2.2), 0)]
def weight (x : Chart) : Fin 3 → ℝ :=
  ![1, (1 - x.2.1 ^ 2) / x.1 ^ 2, 1 / (x.1 ^ 2 * (1 - x.2.1 ^ 2))]
def drift (x : Chart) : Fin 3 → ℝ := ![2 / x.1, -2 * x.2.1 / x.1 ^ 2, 0]

theorem root_sq (μ : ℝ) (hμ : μ ∈ Ioo (-1) 1) : root μ ^ 2 = 1 - μ ^ 2 :=
  Real.sq_sqrt (by nlinarith [hμ.1, hμ.2])
theorem root_pos (μ : ℝ) (hμ : μ ∈ Ioo (-1) 1) : 0 < root μ :=
  Real.sqrt_pos.mpr (by nlinarith [hμ.1, hμ.2])

theorem root_hasDerivAt (μ : ℝ) (hμ : μ ∈ Ioo (-1) 1) :
    HasDerivAt root (-μ / root μ) μ := by
  convert! (((hasDerivAt_id μ).pow 2).const_sub 1).sqrt
    (by nlinarith [hμ.1, hμ.2] : 1 - μ ^ 2 ≠ 0) using 1
  simp only [root, id_eq, Pi.pow_apply]
  ring

theorem root_slope_hasDerivAt (μ : ℝ) (hμ : μ ∈ Ioo (-1) 1) :
    HasDerivAt (fun u => -u / root u) (-1 / root μ ^ 3) μ := by
  have hs := root_sq μ hμ
  have hn := (root_pos μ hμ).ne'
  convert! (hasDerivAt_id μ).neg.div (root_hasDerivAt μ hμ) hn using 1
  simp only [Pi.neg_apply, id_eq]
  field_simp
  nlinarith

theorem replace_self (i : Fin 3) (x : Chart) : replace i x (coord x i) = x := by
  fin_cases i <;> rfl

theorem position_hasDerivAt (i : Fin 3) (x : Chart) (hx : x ∈ chartDomain) :
    HasDerivAt (fun t => position (replace i x t)) (velocity x i) (coord x i) := by
  fin_cases i
  · have h := ((((hasDerivAt_id x.1).mul_const (root x.2.1)).mul_const
      (Real.cos x.2.2)).prodMk
        (((hasDerivAt_id x.1).mul_const (root x.2.1)).mul_const (Real.sin x.2.2))).prodMk
          ((hasDerivAt_id x.1).mul_const x.2.1)
    simpa [position, replace, velocity, coord] using! h
  · have h := ((((root_hasDerivAt x.2.1 hx.2).const_mul x.1).mul_const
      (Real.cos x.2.2)).prodMk
        (((root_hasDerivAt x.2.1 hx.2).const_mul x.1).mul_const (Real.sin x.2.2))).prodMk
          ((hasDerivAt_id x.2.1).const_mul x.1)
    convert! h using 1
    ext <;> dsimp [position, replace, velocity, coord] <;> ring
  · have h := (((Real.hasDerivAt_cos x.2.2).const_mul (x.1 * root x.2.1)).prodMk
        ((Real.hasDerivAt_sin x.2.2).const_mul (x.1 * root x.2.1))).prodMk
          (hasDerivAt_const x.2.2 (x.1 * x.2.1))
    convert! h using 1
    ext <;> dsimp [position, replace, velocity, coord]
    all_goals ring

theorem velocity_hasDerivAt (i : Fin 3) (x : Chart) (hx : x ∈ chartDomain) :
    HasDerivAt (fun t => velocity (replace i x t) i) (acceleration x i) (coord x i) := by
  fin_cases i
  · simpa [velocity, replace, acceleration, coord] using!
      hasDerivAt_const x.1 ((root x.2.1 * Real.cos x.2.2,
        root x.2.1 * Real.sin x.2.2), x.2.1)
  · have h := ((((root_slope_hasDerivAt x.2.1 hx.2).const_mul x.1).mul_const
      (Real.cos x.2.2)).prodMk
        (((root_slope_hasDerivAt x.2.1 hx.2).const_mul x.1).mul_const (Real.sin x.2.2))).prodMk
          (hasDerivAt_const x.2.1 x.1)
    convert! h using 1 <;> ext <;> dsimp [velocity, replace, acceleration, coord] <;> ring
  · have h := (((Real.hasDerivAt_sin x.2.2).const_mul (-x.1 * root x.2.1)).prodMk
        ((Real.hasDerivAt_cos x.2.2).const_mul (x.1 * root x.2.1))).prodMk
          (hasDerivAt_const x.2.2 (0 : ℝ))
    convert! h using 1
    ext <;> dsimp [velocity, replace, acceleration, coord]
    all_goals ring

theorem position_radius (x : Chart) (hx : x ∈ chartDomain) : radius (position x) = x.1 := by
  have hs := root_sq x.2.1 hx.2
  have ht := Real.sin_sq_add_cos_sq x.2.2
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hx.1.le).mp
  change radius (position x) ^ 2 = x.1 ^ 2
  rw [radius_sq]
  dsimp [position]
  calc
    _ = x.1 ^ 2 * (root x.2.1 ^ 2 *
        (Real.sin x.2.2 ^ 2 + Real.cos x.2.2 ^ 2) + x.2.1 ^ 2) := by ring
    _ = x.1 ^ 2 := by rw [ht, hs]; ring

theorem position_off_axis (x : Chart) (hx : x ∈ chartDomain) : (position x).1 ≠ 0 := by
  intro he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp [position] at h1 h2
  have hr := hx.1.ne'
  have hs := (root_pos x.2.1 hx.2).ne'
  have hc : Real.cos x.2.2 = 0 := (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hr hs)
  have hsin : Real.sin x.2.2 = 0 := (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hr hs)
  have ht := Real.sin_sq_add_cos_sq x.2.2
  rw [hc, hsin] at ht
  norm_num at ht

theorem north_connection (g : ℝ) (x : Chart) (hx : x ∈ chartDomain) (i : Fin 3) :
    dot (north g (position x)) (velocity x i) = ![0, 0, g * (1 - x.2.1)] i := by
  have hr := position_radius x hx
  have hs := root_sq x.2.1 hx.2
  have hn := (root_pos x.2.1 hx.2).ne'
  have ht := Real.sin_sq_add_cos_sq x.2.2
  fin_cases i
  · simp [dot_apply, north, position, velocity]
    ring
  · simp [dot_apply, north, position, velocity]
    ring
  · have h := north_contraction g (position x) (position_off_axis x hx)
    rw [hr] at h
    have hc : (position x).2 / x.1 = x.2.1 := by
      dsimp [position]
      field_simp [hx.1.ne']
    rw [hc] at h
    simpa [azimuthalTangent, position, velocity, neg_mul] using h

theorem metric_identity (x : Chart) (hx : x ∈ chartDomain) (j k : Fin 3) :
    ∑ i : Fin 3, weight x i * component (velocity x i) j * component (velocity x i) k =
      if j = k then 1 else 0 := by
  have hs := root_sq x.2.1 hx.2
  have hn := (root_pos x.2.1 hx.2).ne'
  have hr := hx.1.ne'
  have hm : 1 - x.2.1 ^ 2 ≠ 0 := by nlinarith [hx.2.1, hx.2.2]
  have ht : Real.cos x.2.2 ^ 2 = 1 - Real.sin x.2.2 ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x.2.2]
  have hs4 : root x.2.1 ^ 4 = (1 - x.2.1 ^ 2) ^ 2 := by
    calc _ = (root x.2.1 ^ 2) ^ 2 := by ring
         _ = _ := by rw [hs]
  fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_three, weight, velocity, component] <;>
    field_simp [hn, hr, hm] <;> try simp only [hs4, hs, ht]
  all_goals ring

theorem drift_identity (x : Chart) (hx : x ∈ chartDomain) :
    ∑ i : Fin 3, ((weight x i) • acceleration x i + (drift x i) • velocity x i) = 0 := by
  have hs := root_sq x.2.1 hx.2
  have hn := (root_pos x.2.1 hx.2).ne'
  have hr := hx.1.ne'
  have hm : 1 - x.2.1 ^ 2 ≠ 0 := by nlinarith [hx.2.1, hx.2.2]
  have hs4 : root x.2.1 ^ 4 = (1 - x.2.1 ^ 2) ^ 2 := by
    calc _ = (root x.2.1 ^ 2) ^ 2 := by ring
         _ = _ := by rw [hs]
  ext <;> simp [Fin.sum_univ_three, weight, drift, velocity, acceleration, smul_eq_mul] <;>
    field_simp [hn, hr, hm] <;> try simp only [hs4, hs]
  all_goals ring

theorem north_as_azimuthal_velocity (g : ℝ) (x : Chart) (hx : x ∈ chartDomain) :
    north g (position x) =
      (g * (1 - x.2.1) / (x.1 ^ 2 * (1 - x.2.1 ^ 2))) • velocity x 2 := by
  have hr := position_radius x hx
  have hrad := hx.1.ne'
  have hm : 1 - x.2.1 ^ 2 ≠ 0 := by nlinarith [hx.2.1, hx.2.2]
  have hp : 1 + x.2.1 ≠ 0 := by linarith [hx.2.1]
  have hden : x.1 + x.1 * x.2.1 ≠ 0 := by
    have hh := mul_pos hx.1 (show 0 < 1 + x.2.1 by linarith [hx.2.1])
    nlinarith
  have hc : coefficient g (position x) = g / (x.1 * (x.1 + x.1 * x.2.1)) := by
    unfold coefficient
    rw [hr]
    rfl
  simp only [north, hc]
  ext <;> simp [position, velocity, smul_eq_mul] <;>
    field_simp [hrad, hm, hp, hden] <;> ring

theorem north_norm_sq (g : ℝ) (x : Chart) (hx : x ∈ chartDomain) :
    dot (north g (position x)) (north g (position x)) =
      (g * (1 - x.2.1)) ^ 2 / (x.1 ^ 2 * (1 - x.2.1 ^ 2)) := by
  conv_lhs => arg 2; rw [north_as_azimuthal_velocity g x hx]
  rw [map_smul, north_connection g x hx 2]
  change g * (1 - x.2.1) / (x.1 ^ 2 * (1 - x.2.1 ^ 2)) * (g * (1 - x.2.1)) = _
  ring

/-- The ordinary Cartesian divergence, with coordinate derivatives. -/
def divergence (A : Space → Space) (p : Space) : ℝ :=
  deriv (fun t => (A ((t, p.1.2), p.2)).1.1) p.1.1 +
  deriv (fun t => (A ((p.1.1, t), p.2)).1.2) p.1.2 +
  deriv (fun t => (A (p.1, t)).2) p.2

private theorem sqrt_line (a b : ℝ) (h : 0 < a ^ 2 + b) :
    HasDerivAt (fun t => Real.sqrt (t ^ 2 + b)) (a / Real.sqrt (a ^ 2 + b)) a := by
  convert (((hasDerivAt_id a).pow 2).add_const b).sqrt h.ne' using 1
  all_goals simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  all_goals field_simp

private theorem radius_dx (p : Space) (hp : p ≠ 0) :
    HasDerivAt (fun t => radius ((t, p.1.2), p.2)) (p.1.1 / radius p) p.1.1 := by
  have h := sqrt_line p.1.1 (p.1.2 ^ 2 + p.2 ^ 2)
    (by have := radius_pos p hp; have := radius_sq p; nlinarith)
  simpa [MagHK.DiracString.radius, add_assoc] using h

private theorem radius_dy (p : Space) (hp : p ≠ 0) :
    HasDerivAt (fun t => radius ((p.1.1, t), p.2)) (p.1.2 / radius p) p.1.2 := by
  have h := sqrt_line p.1.2 (p.1.1 ^ 2 + p.2 ^ 2)
    (by have := radius_pos p hp; have := radius_sq p; nlinarith)
  simpa [MagHK.DiracString.radius, add_comm, add_left_comm, add_assoc] using h

private theorem coefficient_dx (g : ℝ) (p : Space) (hp : p ∈ northDomain) :
    HasDerivAt (fun t => coefficient g ((t, p.1.2), p.2))
      (-g * p.1.1 * (2 * radius p + p.2) / (radius p ^ 3 * (radius p + p.2) ^ 2)) p.1.1 := by
  have hr := radius_dx p (north_nonzero hp)
  have hd := (hasDerivAt_const p.1.1 g).div (hr.mul (hr.add_const p.2))
    (mul_ne_zero (radius_pos p (north_nonzero hp)).ne' (ne_of_gt hp))
  convert hd using 1 <;> try rfl
  all_goals simp only [Pi.mul_apply]
  all_goals field_simp [(radius_pos p (north_nonzero hp)).ne',
    (show radius p + p.2 ≠ 0 from ne_of_gt hp)]
  all_goals ring

private theorem coefficient_dy (g : ℝ) (p : Space) (hp : p ∈ northDomain) :
    HasDerivAt (fun t => coefficient g ((p.1.1, t), p.2))
      (-g * p.1.2 * (2 * radius p + p.2) / (radius p ^ 3 * (radius p + p.2) ^ 2)) p.1.2 := by
  have hr := radius_dy p (north_nonzero hp)
  have hd := (hasDerivAt_const p.1.2 g).div (hr.mul (hr.add_const p.2))
    (mul_ne_zero (radius_pos p (north_nonzero hp)).ne' (ne_of_gt hp))
  convert hd using 1 <;> try rfl
  all_goals simp only [Pi.mul_apply]
  all_goals field_simp [(radius_pos p (north_nonzero hp)).ne',
    (show radius p + p.2 ≠ 0 from ne_of_gt hp)]
  all_goals ring

theorem north_divergence (g : ℝ) (p : Space) (hp : p ∈ northDomain) :
    divergence (north g) p = 0 := by
  have hx := ((coefficient_dx g p hp).const_mul (-p.1.2)).deriv
  have hy := ((coefficient_dy g p hp).const_mul p.1.1).deriv
  simp only [divergence, north, deriv_const]
  change deriv (fun t => -p.1.2 * coefficient g ((t, p.1.2), p.2)) p.1.1 +
    deriv (fun t => p.1.1 * coefficient g ((p.1.1, t), p.2)) p.1.2 + 0 = 0
  rw [hx, hy]
  ring

theorem position_contDiffAt (x : Chart) (hx : x ∈ chartDomain) :
    ContDiffAt ℝ ∞ position x := by
  have hroot : ContDiffAt ℝ ∞ (fun y : Chart => root y.2.1) x := by
    unfold root
    apply ContDiffAt.sqrt (by fun_prop)
    nlinarith [hx.2.1, hx.2.2]
  exact (((contDiff_fst.contDiffAt.mul hroot).mul
    ((contDiff_snd.snd.cos).contDiffAt)).prodMk
      ((contDiff_fst.contDiffAt.mul hroot).mul
        ((contDiff_snd.snd.sin).contDiffAt))).prodMk
          (contDiff_fst.contDiffAt.mul (contDiff_snd.fst.contDiffAt))

theorem replace_contDiff (i : Fin 3) (x : Chart) : ContDiff ℝ ∞ (replace i x) := by
  change ContDiff ℝ ∞ (fun t => replace i x t)
  fin_cases i <;> dsimp [replace] <;> fun_prop

theorem curve_contDiffAt (i : Fin 3) (x : Chart) (hx : x ∈ chartDomain) :
    ContDiffAt ℝ 2 (fun t => position (replace i x t)) (coord x i) := by
  have hp : ContDiffAt ℝ ∞ position (replace i x (coord x i)) := by
    rw [replace_self]
    exact position_contDiffAt x hx
  exact (hp.comp (coord x i) ((replace_contDiff i x).contDiffAt)).of_le (by simp)

@[simp] theorem coord_replace (i : Fin 3) (x : Chart) (t : ℝ) :
    coord (replace i x t) i = t := by fin_cases i <;> rfl
@[simp] theorem replace_replace (i : Fin 3) (x : Chart) (s t : ℝ) :
    replace i (replace i x s) t = replace i x t := by fin_cases i <;> rfl

theorem isOpen_chartDomain : IsOpen chartDomain :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_Ioo.preimage (continuous_snd.fst))

theorem curve_second_derivative (i : Fin 3) (x : Chart) (hx : x ∈ chartDomain) :
    deriv (deriv (fun t => position (replace i x t))) (coord x i) = acceleration x i := by
  have hmap : Filter.Tendsto (replace i x) (nhds (coord x i)) (nhds x) := by
    simpa only [replace_self] using ((replace_contDiff i x).continuous.tendsto (coord x i))
  have he : deriv (fun t => position (replace i x t)) =ᶠ[nhds (coord x i)]
      (fun t => velocity (replace i x t) i) := by
    filter_upwards [hmap.eventually (isOpen_chartDomain.mem_nhds hx)] with t ht
    simpa only [coord_replace, replace_replace] using (position_hasDerivAt i (replace i x t) ht).deriv
  exact he.deriv_eq.trans (velocity_hasDerivAt i x hx).deriv

theorem north_directional_derivative (g : ℝ) (F : Space → ℂ) (x : Chart)
    (hx : x ∈ chartDomain) (hF : DifferentiableAt ℝ F (position x)) :
    fderiv ℝ F (position x) (north g (position x)) =
      (g * (1 - x.2.1) / (x.1 ^ 2 * (1 - x.2.1 ^ 2))) • Dphi (F ∘ position) x := by
  rw [north_as_azimuthal_velocity g x hx, map_smul]
  congr 1
  have h := hF.hasFDerivAt.comp_hasDerivAt (coord x 2) (position_hasDerivAt 2 x hx)
  have he : Dphi (F ∘ position) x = fderiv ℝ F (position x) (velocity x 2) := by
    simpa [Function.comp_def, Dphi, MagHK.MonopoleAngular.Dφ, replace, coord] using h.deriv
  exact he.symm

end MagHK.MonopoleCartesianDifferential
