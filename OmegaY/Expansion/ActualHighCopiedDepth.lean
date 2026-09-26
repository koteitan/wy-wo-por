/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighCopiedDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighTerminalDepth
import OmegaY.Expansion.ActualHighFixedPathDepth
import OmegaY.Expansion.ActualHighRootPathDepth

/-!
# Actual absolute high-event depth of an effective copied occurrence

The certificate retains the genuine copied node, its actual frontier and
the high-event sampling, together with absolute depth equality. The depth
is in the stored-parent event forest; this does not assert numerical-parent
recognition or well-foundedness of successive expansions.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

structure HighCopiedDepth {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (source : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat)
    (copy : EffectiveCopyOccurrence p block start references source ambient) where
  source_width : 0 < p.reduced.size
  target_width : 0 < ambient.size
  targetEvent : Nat
  targetNode : (Frame.ofMountain ambient).Node
  target_event_start : (Frame.ofMountain ambient).highEventStart p.lastTop.row ≤ targetEvent
  target_event_end : targetEvent ≤ (Frame.ofMountain ambient).lastEvent
  event_row : (Frame.ofMountain ambient).eventCut targetEvent =
    (Frame.ofMountain p.reduced).eventCut sourceEvent
  event_index : (Frame.ofMountain p.reduced).highEventStart p.lastTop.row +
    (targetEvent - (Frame.ofMountain ambient).highEventStart p.lastTop.row) = sourceEvent
  reference : Frame.ref targetNode = copy.outputRef
  cell : (Frame.ofMountain ambient).cell targetNode = copy.read.outputCell
  frontier : eventFrontier s.ambient_valid.toOrdered targetEvent targetNode.1 = targetNode
  absolute_depth : parentDepth
      (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent)
        targetNode.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
      (p.reduced.size - 1) sourceEvent) source.1.val

def HighCopiedPathDepth.toAbsolute
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references p.reduced.size ambient}
    {source parent : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {copy : EffectiveCopyOccurrence p block start references source ambient}
    {parentCopy : EffectiveCopyOccurrence p block start references parent ambient}
    (packet : HighCopiedPathDepth s source parent sourceEvent copy parentCopy)
    (hDepth : parentDepth
        (eventParentMap s.ambient_valid.toOrdered packet.target_width (ambient.size - 1) packet.targetEvent)
          packet.childNode.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
        (p.reduced.size - 1) sourceEvent) source.1.val) :
    HighCopiedDepth s source sourceEvent copy where
  source_width := packet.source_width
  target_width := packet.target_width
  targetEvent := packet.targetEvent
  targetNode := packet.childNode
  target_event_start := packet.target_event_start
  target_event_end := packet.target_event_end
  event_row := packet.event_row
  event_index := packet.event_index
  reference := packet.child_reference
  cell := packet.child_cell
  frontier := packet.child_frontier
  absolute_depth := hDepth

/-- A certificate's depth equality is independent of the target event
number: only its actual cut matters. This permits later actual samplings
and preserved-prefix arguments without supplying a new frontier. -/
theorem HighCopiedDepth.at_equal_cut
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references p.reduced.size ambient}
    {source : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {copy : EffectiveCopyOccurrence p block start references source ambient}
    (packet : HighCopiedDepth s source sourceEvent copy)
    {targetEvent : Nat}
    (hCut : (Frame.ofMountain ambient).eventCut targetEvent =
      (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered packet.target_width
        (ambient.size - 1) targetEvent) copy.outputRef.column =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        packet.source_width (p.reduced.size - 1) sourceEvent) source.1.val := by
  have hPreserve : PreservesColumns ambient ambient := fun _ _ => rfl
  have hSame := hPreserve.event_parentDepth s.ambient_valid.toOrdered s.ambient_valid.toOrdered
    packet.target_width packet.target_width (hCut.trans packet.event_row.symm) packet.targetNode.1.isLt
  have hColumn : packet.targetNode.1.val = copy.outputRef.column := congrArg Ref.column packet.reference
  rw [← hColumn, hSame]
  exact packet.absolute_depth

theorem DynamicBlockState.actual_high_copied_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block startCopies copies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hAmbientRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok ambient)
    {source : (Frame.ofMountain p.reduced).Node}
    (hRight : p.root.column < source.1.val)
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent source.1 = source) :
    Nonempty (HighCopiedDepth s source sourceEvent copy) := by
  rcases Frame.parent_path_exit (build_normal_of_success p.reduced_build).toOrdered hRight with
    ⟨terminal, path, hTerminalRight, hNone⟩ |
    ⟨root, path, hRootColumn⟩ | ⟨lastBad, fixed, path, hBadRight, hExit, hFixed⟩
  · obtain ⟨terminalCopy⟩ := s.prior_effective_occurrence history hLast hTerminalRight terminal.1.isLt
    obtain ⟨packet⟩ := s.actual_high_path_depth history hLast hAmbientRun path hTerminalRight
      copy terminalCopy hSourceEvent hHigh hSourceFront
    exact ⟨packet.toAbsolute (packet.terminal_depths hLast hNone).2.2⟩
  · obtain ⟨lastBad, _, _, ⟨packet⟩⟩ := s.actual_high_root_path_depth_of_path history hLast
      hStartRun hAmbientRun path hRootColumn hRight copy hSourceEvent hHigh hSourceFront
    exact ⟨packet.copied.toAbsolute packet.absolute_depth⟩
  · obtain ⟨packet⟩ := s.actual_high_fixed_path_depth history hLast hAmbientRun path hExit
      hBadRight hFixed copy hSourceEvent hHigh hSourceFront
    exact ⟨packet.copied.toAbsolute packet.absolute_depth⟩

/-- At every high source event the entire newly copied column has the
source column's absolute forest depth at the same target cut. The source
frontier and its actual effective occurrence are constructed internally;
all three possible exits of its parent chain are covered. -/
theorem DynamicBlockState.actual_high_column_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block startCopies copies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hAmbientRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok ambient)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {sourceColumn : Fin (Frame.ofMountain p.reduced).width}
    (hRight : p.root.column < sourceColumn.val)
    {sourceEvent targetEvent : Nat}
    (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hCut : (Frame.ofMountain ambient).eventCut targetEvent =
      (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        (sourceColumn.val + block * (p.reduced.size - 1 - p.root.column)) =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) sourceColumn.val := by
  let source := eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent sourceColumn
  have hSourceColumn : source.1.val = sourceColumn.val := rfl
  obtain ⟨copy⟩ := s.prior_effective_occurrence history hLast (hSourceColumn ▸ hRight) source.1.isLt
  obtain ⟨packet⟩ := s.actual_high_copied_depth history hLast hStartRun hAmbientRun
    (hSourceColumn ▸ hRight) copy hSourceEvent hHigh (show eventFrontier
      (build_normal_of_success p.reduced_build).toOrdered sourceEvent source.1 = source from rfl)
  simpa only [copy.source_column, hSourceColumn] using packet.at_equal_cut hCut

end OmegaY.Expansion

#print axioms OmegaY.Expansion.HighCopiedDepth.at_equal_cut
#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_copied_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_column_depth
