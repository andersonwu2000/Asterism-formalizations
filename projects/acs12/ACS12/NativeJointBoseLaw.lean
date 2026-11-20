import ACS12.JointDifferentiatedBoseLaw

/-! The full joint law follows from one differentiated-Laplace strip at each positive shape. -/
namespace ACS12.NativeCells
open MeasureTheory

theorem boseRow_joint_all {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    boseRow p N = N^2*nativeJointScale p*
      ∫ s, nativeJointEnergy (N^2) s^((p-2)/2) ∂nativeJointMeasure p :=
  boseRow_joint_differentiated hp hN

end ACS12.NativeCells
