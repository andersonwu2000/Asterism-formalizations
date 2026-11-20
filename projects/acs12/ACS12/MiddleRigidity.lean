import ACS12.MiddleLowConsumer
import ACS12.JointActualReceiver
import ACS12.FourSiteExchange
import ACS12.ShortCycle
import ACS12.ChartDescent


namespace ACS12

open GammaMeasure

theorem Configuration.rigidity_middle {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 1 ≤ p) (hP : p ≤ 9 / 5) : IsEqualMassRegular F := by
  have hp₀ := zero_lt_one.trans_le hp
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  rcases eq_or_lt_of_le hn with rfl | hn
  · exact F.two_sites_regular hp₀.le
  rcases eq_or_lt_of_le (show 3 ≤ n by omega) with rfl | hn
  · exact F.three_sites_regular hp₀.le
  rcases eq_or_lt_of_le (show 4 ≤ n by omega) with rfl | hn
  · exact F.four_sites_regular hp₀
  by_contra hN
  obtain ⟨C⟩ := F.exists_normalized_chart (by omega)
  obtain ⟨j,hj⟩ := C.source.exists_third (by simpa using (show 3 ≤ n by omega))
  obtain ⟨k,hk⟩ := C.source.exists_fourth (by simpa using (show 4 ≤ n by omega)) hj
  have hu₁ := F.next_gap_lt_one (by omega) hp₀ hp₂ hN C hj
  have huL := F.first_gap_gt_sevenEighths (by omega) hp hP C hj hk hu₁
  rcases le_total (C.source.forwardDistance j k) (C.source.forwardDistance C.source.neighbor j) with h | h
  · exact F.inner_actual_high_impossible (by omega) hp hP C hj hk huL.le hu₁ h
  · exact F.outer_actual_high_impossible (by omega) hp hP C hj hk huL.le hu₁ h

end ACS12
