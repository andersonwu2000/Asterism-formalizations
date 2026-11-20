import CenteredCircle.TorquePeriodization

/-!
A finite anchored source and its actual periodic exterior images. The data
structure contains no force equation or desired rigidity conclusion.
-/

namespace CenteredCircle.AllN

open scoped BigOperators

noncomputable def imageTail (K : ℝ → ℝ) (L t : ℝ) : ℝ :=
  ∑' j : ℕ, K (t + j * L)

theorem imageTail_split (K : ℝ → ℝ) (L t : ℝ)
    (hs : Summable (fun j : ℕ => K (t + j * L))) :
    imageTail K L t = K t + imageTail K L (t + L) := by
  have h := hs.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_mul, add_zero] at h
  rw [imageTail, h]
  congr 1
  apply tsum_congr
  intro j
  dsimp only
  congr 1
  push_cast
  ring

theorem imageTail_shift (K : ℝ → ℝ) (L t a : ℝ) :
    imageTail (fun x => K (x + a)) L t = imageTail K L (t + a) := by
  apply tsum_congr
  intro j
  congr 1
  ring

theorem radial_image_pair {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htL : t < L) :
    imageTail (radialKernel L) L t + imageTail (radialKernel L) L (L - t) =
      periodicRadialKernel L t := by
  rw [periodicRadialKernel_eq_tails hL ht htL,
    radialImageTail_eq_tsum hL ht, radialImageTail_eq_tsum hL (sub_pos.mpr htL)]
  rfl

theorem torque_image_pair {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (htL : t < L) :
    imageTail (torqueKernel L) L t - imageTail (torqueKernel L) L (L - t) =
      -deriv (periodicRadialKernel L) t := by
  rw [periodicRadialKernel_deriv_torque hL ht htL]
  dsimp [imageTail]
  ring

structure AnchoredCircleSource (ι : Type*) where
  period : ℝ
  period_ge_two : 2 ≤ period
  coordinate : ι → ℝ
  mass : ι → ℝ
  root : ι
  neighbor : ι
  coordinate_root : coordinate root = 0
  coordinate_neighbor : coordinate neighbor = 1
  coordinate_nonneg : ∀ i, 0 ≤ coordinate i
  coordinate_lt_period : ∀ i, coordinate i < period
  other_coordinate : ∀ i, i ≠ root → i ≠ neighbor → 1 < coordinate i
  coordinate_injective : Function.Injective coordinate
  mass_pos : ∀ i, 0 < mass i
  mass_root : mass root = 1
  mass_neighbor_le_one : mass neighbor ≤ 1

namespace AnchoredCircleSource

variable {ι : Type*} (F : AnchoredCircleSource ι)

theorem period_pos : 0 < F.period := lt_of_lt_of_le (by norm_num) F.period_ge_two

theorem root_ne_neighbor : F.root ≠ F.neighbor := by
  intro h
  have he := congrArg F.coordinate h
  rw [F.coordinate_root, F.coordinate_neighbor] at he
  norm_num at he

variable [DecidableEq ι]

noncomputable def leftDistance (i : ι) : ℝ := F.period - F.coordinate i

noncomputable def rightDistance (i : ι) : ℝ :=
  if i = F.root ∨ i = F.neighbor then F.coordinate i + F.period - 1
  else F.coordinate i - 1

theorem leftDistance_pos (i : ι) : 0 < F.leftDistance i :=
  sub_pos.mpr (F.coordinate_lt_period i)

theorem rightDistance_pos (i : ι) : 0 < F.rightDistance i := by
  unfold rightDistance
  split_ifs with h
  · have hc := F.coordinate_nonneg i
    have hL := F.period_ge_two
    linarith
  · have hh := F.other_coordinate i (fun hi => h (Or.inl hi)) (fun hi => h (Or.inr hi))
    linarith

theorem coordinate_pos_of_ne_root {i : ι} (hi : i ≠ F.root) : 0 < F.coordinate i := by
  by_cases hj : i = F.neighbor
  · rw [hj, F.coordinate_neighbor]
    norm_num
  · linarith [F.other_coordinate i hi hj]

theorem rightDistance_lt_period {i : ι} (hi : i ≠ F.neighbor) : F.rightDistance i < F.period := by
  by_cases hj : i = F.root
  · simp only [rightDistance, hj, true_or, ite_true, F.coordinate_root, zero_add]
    linarith
  · simp only [rightDistance, hj, hi, false_or, ite_false]
    linarith [F.coordinate_lt_period i]

variable [Fintype ι]

noncomputable def leftExterior (K : ℝ → ℝ) : ℝ :=
  ∑ i, F.mass i * imageTail K F.period (F.leftDistance i)

noncomputable def rightExterior (K : ℝ → ℝ) : ℝ :=
  ∑ i, F.mass i * imageTail K F.period (F.rightDistance i)

noncomputable def rootRadialRow : ℝ :=
  ∑ i ∈ Finset.univ.erase F.root, F.mass i * periodicRadialKernel F.period (F.coordinate i)

noncomputable def neighborRadialRow : ℝ :=
  ∑ i ∈ Finset.univ.erase F.neighbor, F.mass i * periodicRadialKernel F.period (F.rightDistance i)

noncomputable def rootTorqueRow : ℝ :=
  ∑ i ∈ Finset.univ.erase F.root, F.mass i * deriv (periodicRadialKernel F.period) (F.coordinate i)

noncomputable def neighborTorqueRow : ℝ :=
  ∑ i ∈ Finset.univ.erase F.neighbor, F.mass i * deriv (periodicRadialKernel F.period) (F.rightDistance i)

end AnchoredCircleSource

end CenteredCircle.AllN
