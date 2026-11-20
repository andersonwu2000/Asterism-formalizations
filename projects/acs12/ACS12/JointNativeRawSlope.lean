import ACS12.JointNativeTiltMoments

/-! The joint tilted mean is exactly the logarithmic count slope of the original raw Bose row. -/
namespace ACS12.NativeCells
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem boseRow_joint_log_hasDerivAt {p N : ℝ} (hp : 2 ≤ p) (hN : 0 < N) :
    HasDerivAt (fun x => Real.log (boseRow p x))
      ((2+(p-2)*jointNativeMean p (N^2))/N) N := by
  let β := (p-2)/2
  let F := jointPowerRow p β
  have hp₀ : 0 < p := by linarith only [hp]
  have hβ : 0 ≤ β := by dsimp only [β]; linarith only [hp]
  have hFPos : 0 < F (N^2) := jointPowerRow_pos hp₀ (sq_nonneg N)
  have hC := nativeJointScale_pos hp₀
  have hSquare : HasDerivAt (fun x : ℝ => x^2) (2*N) N := by
    convert (hasDerivAt_id N).pow 2 using 1 <;> simp
  have hFD : HasDerivAt F (β*jointWeightedPowerRow p β 1 (N^2)) (N^2) :=
    jointPowerRow_hasDerivAt hp₀ hβ (sq_pos_of_pos hN)
  have hNF : HasDerivAt (fun x : ℝ => F (x^2))
      ((β*jointWeightedPowerRow p β 1 (N^2))*(2*N)) N := hFD.comp_of_eq N hSquare rfl
  have hNFLog := hNF.log hFPos.ne'
  have hNLog := ((hasDerivAt_id N).log hN.ne').const_mul 2
  let G (x : ℝ) := 2*Real.log x+Real.log (nativeJointScale p)+Real.log (F (x^2))
  have hRaw := (hNLog.add_const (Real.log (nativeJointScale p))).add hNFLog
  have hEq : (fun x => Real.log (boseRow p x)) =ᶠ[𝓝 N] G := by
    filter_upwards [Ioi_mem_nhds hN] with x hx
    have hFP : 0 < F (x^2) := jointPowerRow_pos hp₀ (sq_nonneg x)
    rw [boseRow_joint_all hp₀ hx]
    change Real.log (x^2*nativeJointScale p*F (x^2)) = G x
    rw [Real.log_mul (mul_pos (sq_pos_of_pos hx) hC).ne' hFP.ne',
      Real.log_mul (sq_pos_of_pos hx).ne' hC.ne',Real.log_pow]
    dsimp only [G,F,β]
    norm_num only [Nat.cast_ofNat]
  have h := hRaw.congr_of_eventuallyEq hEq
  convert h using 1
  rw [jointNativeMean_weighted hp₀ (sq_pos_of_pos hN)]
  dsimp only [id_eq,Pi.pow_apply,β,F]
  norm_num only [Nat.cast_ofNat,pow_one,mul_one]
  field_simp [hN.ne',hFPos.ne']
  <;> ring

theorem boseRow_joint_rawElasticity {p N : ℝ} (hp : 2 ≤ p) (hN : 0 < N) :
    N*deriv (fun x => Real.log (boseRow p x)) N =
      2+(p-2)*jointNativeMean p (N^2) := by
  rw [(boseRow_joint_log_hasDerivAt hp hN).deriv]
  field_simp [hN.ne']

end ACS12.NativeCells
