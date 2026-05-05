import Windmill.Certificate

namespace Windmill

def exported : Certificate :=
  {
    points := #[
      { x := 1, y := -4 },
    { x := 49, y := -44 },
    { x := 91, y := -89 },
    { x := 74, y := -76 },
    { x := 64, y := -74 },
    { x := 86, y := -76 },
    { x := 225, y := -212 }
    ]
    cycle := #[
      { prev := 0, curr := 6 },
    { prev := 6, curr := 2 },
    { prev := 2, curr := 3 },
    { prev := 3, curr := 4 },
    { prev := 4, curr := 5 },
    { prev := 5, curr := 3 },
    { prev := 3, curr := 1 },
    { prev := 1, curr := 2 },
    { prev := 2, curr := 0 }
    ]
    cover := #[8, 6, 1, 2, 3, 4, 0]
  }

theorem exported_valid : check exported = true := by
  decide

theorem exported_covers_points :
    ∀ i : Fin exported.points.size, ∃ j : Fin exported.cycle.size, (exported.cycle[j]).curr = i.val := by
  decide

end Windmill
