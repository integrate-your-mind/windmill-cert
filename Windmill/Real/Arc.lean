import Windmill.Real.Median

noncomputable section

namespace Windmill
namespace Real

def InOpenArc (pivot start stop test : Point) : Prop :=
  if orient pivot start stop > 0 then
    orient pivot start test > 0 ∧ orient pivot test stop > 0
  else
    orient pivot start test > 0 ∨ orient pivot test stop > 0

lemma not_inOpenArc_self_stop (pivot start stop : Point) :
    ¬ InOpenArc pivot start stop stop := by
  unfold InOpenArc
  by_cases h : orient pivot start stop > 0
  · simp [h]
  · simp [h]

lemma not_inOpenArc_self_start (pivot start stop : Point) :
    ¬ InOpenArc pivot start stop start := by
  unfold InOpenArc
  by_cases h : orient pivot start stop > 0
  · simp [h]
  · simp [h]

end Real
end Windmill
