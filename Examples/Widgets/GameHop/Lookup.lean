module

public meta import Examples.Widgets.GameHop.Hints
public meta import Examples.Widgets.GameHop.Registry
public meta import Examples.Widgets.GameHop.Infer

public meta section

namespace VCVioWidgets
namespace GameHop

/-- Compatibility wrapper while the panel transitions to inferred diagrams. -/
abbrev diagramForModule? := inferDiagramForModule?

end GameHop
end VCVioWidgets
