import ACS12.PressureRowShape
import ACS12.PressureMoments
import Mathlib.Analysis.Convex.Jensen

/-! The row-log surplus under the original two-marginal law and its finite tilt. -/
namespace ACS12.Pressure

open Set
open scoped BigOperators

private theorem tiltedCenter_nonpos {ι : Type*} [Fintype ι] {w X : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i = 1) (hX : ∑ i, w i * X i = 0)
    {c : ℝ} (hc : 0 ≤ c) :
    (∑ i, w i * Real.exp (-c * X i) * X i) ≤ 0 := by
  let e (x : ℝ) := Real.exp (-c * x)
  have hE : Antitone e := by
    intro x y hxy
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr hc))
  have hAtom (i j : ι) : 0 ≤ w i * w j * ((X i - X j) * (e (X j) - e (X i))) := by
    apply mul_nonneg (mul_nonneg (hw i) (hw j))
    rcases le_total (X i) (X j) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr (hE h))
    · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (hE h))
  have hId (i j : ι) : w i * w j * ((X i - X j) * (e (X j) - e (X i))) =
      (w i * X i) * (w j * e (X j)) - (w i * e (X i) * X i) * w j -
        w i * (w j * e (X j) * X j) + (w i * e (X i)) * (w j * X j) := by ring
  have h : 0 ≤ ∑ i, ∑ j, w i * w j * ((X i - X j) * (e (X j) - e (X i))) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hAtom i j
  have hInner (i : ι) :
      (∑ j, w i * w j * ((X i - X j) * (e (X j) - e (X i)))) =
        (w i * X i) * (∑ j, w j * e (X j)) - w i * e (X i) * X i -
          w i * (∑ j, w j * e (X j) * X j) := by
    simp only [hId,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hW,hX,mul_one,mul_zero,add_zero]
  simp only [hInner,Finset.sum_sub_distrib,← Finset.sum_mul,hW,hX,zero_mul,one_mul,zero_sub] at h
  change (∑ i, w i * e (X i) * X i) ≤ 0
  linarith only [h]

/-- The finite tilted law has a strictly positive row surplus for a nonconstant word. -/
theorem pressureRow_surplus_pos {n : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (hn : 0 < n)
    {m : Fin n → ℝ} (hm : ∀ i, 0 < m i) (hm' : ∃ i j, m i ≠ m j)
    {pair : Fin n → Fin n → ℝ} (hPair : ∀ i j, 0 ≤ pair i j)
    (hL : ∀ i, ∑ j, pair i j = massWeight m i)
    (hR : ∀ j, ∑ i, pair i j = massWeight m j)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hs : ∀ i, 0 < s₀ + centeredLogMass m i) :
    let X := centeredLogMass m
    let c := (p - 1) / (2 * (p + 1))
    let tilt (i j : Fin n) := pair i j * Real.exp (-c * (X i + X j))
    let Q := ∑ i, ∑ j, tilt i j
    let φ (x : ℝ) := Real.log (pressureLogCountRow p x)
    0 < (∑ i, ∑ j, tilt i j * ((1 / (p + 1)) *
      (φ s₀ - (φ (s₀ + X i) + φ (s₀ + X j)) / 2))) / Q := by
  dsimp only
  let X := centeredLogMass m
  let c := (p - 1) / (2 * (p + 1))
  let tilt (i j : Fin n) := pair i j * Real.exp (-c * (X i + X j))
  let Q := ∑ i, ∑ j, tilt i j
  let φ (x : ℝ) := Real.log (pressureLogCountRow p x)
  let a := 1 / (p + 1)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr hp.le) (by positivity)
  change 0 < (∑ i, ∑ j, tilt i j * (a * (φ s₀ - (φ (s₀ + X i) + φ (s₀ + X j)) / 2))) / Q
  have hTilt (i j : Fin n) : 0 ≤ tilt i j := mul_nonneg (hPair i j) (Real.exp_pos _).le
  have hTiltRow (i : Fin n) : 0 < ∑ j, tilt i j := by
    have hP : 0 < ∑ j, pair i j := by
      rw [hL]; exact div_pos (hm i) (massTotal_pos hn hm)
    obtain ⟨j,_,hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hPair i j)).mp hP
    exact (mul_pos hj (Real.exp_pos _)).trans_le
      (Finset.single_le_sum (fun k _ => hTilt i k) (Finset.mem_univ j))
  have hQ : 0 < Q := Finset.sum_pos (fun i _ => hTiltRow i) ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have hCent : (∑ i, ∑ j, tilt i j * (X i + X j)) ≤ 0 := by
    let w (k : Fin n × Fin n) := pair k.1 k.2
    let Y (k : Fin n × Fin n) := X k.1 + X k.2
    have hW : ∑ k, w k = 1 := by
      rw [Fintype.sum_prod_type]
      simpa only [w,hL] using massWeight_sum_one hn hm
    have hY : ∑ k, w k * Y k = 0 := by
      rw [Fintype.sum_prod_type]
      simp only [w,Y,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hL]
      rw [Finset.sum_comm (f := fun i j => pair i j * X j)]
      simp only [← Finset.sum_mul,hR,centeredLogMass_mean_zero hn hm,add_zero,X]
    have h := tiltedCenter_nonpos (fun k : Fin n × Fin n => hPair k.1 k.2) hW hY hc
    simpa only [Fintype.sum_prod_type,w,Y,tilt] using h
  let r (i : Fin n) := (∑ j, tilt i j) + ∑ j, tilt j i
  have hr (i : Fin n) : 0 < r i :=
    add_pos_of_pos_of_nonneg (hTiltRow i) (Finset.sum_nonneg fun j _ => hTilt j i)
  have hCollapse (f : Fin n → ℝ) :
      (∑ i, r i * f i) = ∑ i, ∑ j, tilt i j * (f i + f j) := by
    simp only [r,add_mul,mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm (f := fun i j => tilt i j * f j)]
    simp only [← Finset.sum_mul]
  have hSumR : ∑ i, r i = 2 * Q := by
    have h := hCollapse (fun _ => 1)
    norm_num only [mul_one,← Finset.sum_mul] at h
    simpa only [Q,mul_comm] using h
  let w (i : Fin n) := r i / (2 * Q)
  have hw (i : Fin n) : 0 < w i := div_pos (hr i) (by positivity)
  have hW : ∑ i, w i = 1 := by
    simp only [w,← Finset.sum_div,hSumR,div_self (show 2 * Q ≠ 0 by positivity)]
  have hWMean (f : Fin n → ℝ) :
      (∑ i, w i * f i) = (∑ i, ∑ j, tilt i j * (f i + f j)) / (2 * Q) := by
    simp only [w,div_mul_eq_mul_div,← Finset.sum_div,hCollapse]
  have hM : (∑ i, w i * (s₀ + X i)) ≤ s₀ := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hW,one_mul]
    rw [hWMean X]
    exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hCent (by positivity))
  have hM₀ : 0 < ∑ i, w i * (s₀ + X i) :=
    Finset.sum_pos (fun i _ => mul_pos (hw i) (hs i)) ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  obtain ⟨i,j,hij⟩ := hm'
  have hX : X i ≠ X j := by
    have hg : 0 < massGeometricMean m := Real.exp_pos _
    simp only [X,centeredLogMass,Real.log_div hg.ne' (hm _).ne']
    exact fun h => hij (Real.log_injOn_pos (hm i) (hm j) (by linarith only [h]))
  have hJ := (pressureLogCount_log_strictConcave hp hp₂).lt_map_sum
    (t := Finset.univ) (w := w) (p := fun i => s₀ + X i) (fun i _ => hw i) hW
    (fun i _ => hs i) ⟨i,Finset.mem_univ _,j,Finset.mem_univ _,fun h => hX (add_left_cancel h)⟩
  simp only [smul_eq_mul] at hJ
  have hMon : MonotoneOn φ (Ioi 0) := by
    intro x hx y hy h
    exact Real.log_le_log (pressureLogCountRow_pos (zero_lt_one.trans hp) hx)
      ((pressureLogCountRow_shape hp hp₂).2.monotoneOn hx hy h)
  have hPrice : (∑ i, w i * φ (s₀ + X i)) < φ s₀ :=
    hJ.trans_le (hMon hM₀ hs₀ hM)
  rw [hWMean] at hPrice
  have hP := (div_lt_iff₀ (show 0 < 2 * Q by positivity)).mp hPrice
  apply div_pos _ hQ
  have hId (i j : Fin n) : tilt i j * (a * (φ s₀ - (φ (s₀ + X i) + φ (s₀ + X j)) / 2)) =
      tilt i j * (a * φ s₀) - (a / 2) * (tilt i j * (φ (s₀ + X i) + φ (s₀ + X j))) := by ring
  simp_rw [hId,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum]
  change 0 < Q * (a * φ s₀) - (a / 2) * (∑ i, ∑ j, tilt i j * (φ (s₀ + X i) + φ (s₀ + X j)))
  exact sub_pos.mpr (by nlinarith only [mul_lt_mul_of_pos_left hP (show 0 < a / 2 by positivity)])

end ACS12.Pressure

