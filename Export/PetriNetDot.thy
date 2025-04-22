theory PetriNetDot
  imports
    PortGraph.PortGraph
    Show.Show_Instances
begin

section\<open>Export into Dot of Petri Net\<close>

text\<open>
  We can export port graphs into a Dot graph representing a Petri net.
\<close>

locale portGraphPN =
  fixes pathToString :: "'p list \<Rightarrow> String.literal"
    and labelToString :: "'l \<Rightarrow> String.literal"
    and portDataToString :: "'a \<Rightarrow> String.literal"
    and portSideToString :: "'s \<Rightarrow> String.literal"
begin

(* Turn a node into a transition *)
(* TODO fix a function to decide whether it should be immediate from the node label *)
definition nodeToPN :: "'p list \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> String.literal"
  where "nodeToPN prefix n =
  pathToString (prefix @ node_name n) +
  STR ''[label=\"\",xlabel=\"'' + labelToString (node_label n) + STR ''\",shape=box];''"

primrec groundPlaceToNodeID :: "'p list \<Rightarrow> ('s, 'a, 'p) place \<Rightarrow> String.literal"
  where
    "groundPlaceToNodeID prefix (GroundPort qp) = pathToString (prefix @ qualified_port.name qp)"
  | "groundPlaceToNodeID prefix (OpenPort p) = undefined"

primrec placeToID :: "'p list \<Rightarrow> ('s, 'a, 'p) place \<Rightarrow> String.literal"
  where
    "placeToID prefix (GroundPort qp) =
      pathToString (prefix @ qualified_port.name qp) +
      portSideToString (port.side (qualified_port.port qp)) +
      String.implode (show (port.index (qualified_port.port qp)))"
  | "placeToID prefix (OpenPort p) = STR ''open'' + portSideToString (port.side p) + String.implode (show (port.index p))"

(*
  Turn an edge into a PN place, with an incoming arc for the source place if it is on a node and
  an outgoing arc for the target place if its on a node.
  The other parts of those arcs are IDs of the node that place is attached to (which turns into a transition).
 *)
definition edgeToPN :: "'p list \<Rightarrow> ('s, 'a, 'p) edge \<Rightarrow> String.literal"
  where "edgeToPN prefix e =
  placeToID prefix (edge_from e) + STR ''_'' + placeToID prefix (edge_to e) +
  STR ''[width=0.1,label=\"'' + portDataToString (port.label (place_port (edge_from e))) + STR ''\",shape=circle];'' +
  ( if place_ground (edge_from e)
      then  groundPlaceToNodeID prefix (edge_from e) +
            STR '' -> '' +
            placeToID prefix (edge_from e) + STR ''_'' + placeToID prefix (edge_to e) + STR '';''
      else STR ''''
  ) +
  ( if place_ground (edge_to e)
      then  placeToID prefix (edge_from e) + STR ''_'' + placeToID prefix (edge_to e) +
            STR '' -> '' +
            groundPlaceToNodeID prefix (edge_to e) + STR '';''
      else STR ''''
  )"

(* Dropping edges incident on open places for now, because those would need a top-level hierarchical node to attach to *)

definition portGraphToPN :: "'p list \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> String.literal"
  where "portGraphToPN prefix G =
  STR ''digraph {rankdir=\"LR\";'' +
  sum_list (map (nodeToPN prefix) (pg_nodes G)) +
  sum_list (map (edgeToPN prefix) (pg_edges G)) +
  STR ''}''"
end

end
