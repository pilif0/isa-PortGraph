theory ELKJson
  imports
    PortGraph.PortGraph
    Nano_JSON.Nano_JSON_Main
    Show.Show_Instances
begin

section\<open>Export into ELK\<close>

text\<open>
  We can export port graphs into the Eclipse Layout Kernel by generating a JSON object.
\<close>

text\<open>Define ELK notion of port sides (see @{url "https://eclipse.dev/elk/reference/options/org-eclipse-elk-port-side.html"})\<close>
datatype elk_side = UNDEFINED | NORTH | EAST | SOUTH | WEST

primrec portSideToString :: "elk_side \<Rightarrow> String.literal"
  where
    "portSideToString UNDEFINED = STR ''UNDEFINED''"
  | "portSideToString NORTH = STR ''NORTH''"
  | "portSideToString EAST = STR ''EAST''"
  | "portSideToString SOUTH = STR ''SOUTH''"
  | "portSideToString WEST = STR ''WEST''"

text\<open>Map any in-out sides to have @{const In} at @{const WEST} and @{const Out} at @{const EAST}\<close>
fun sideInOutToELK :: "'s :: side_in_out \<Rightarrow> elk_side"
  where "sideInOutToELK x = (if x = In then WEST else if x = Out then EAST else UNDEFINED)"

text\<open>
  ELK port graph construction uses translation of node paths, labels and port sides.
  Note that if the sides satisfy @{class side_in_out} then @{const sideInOutToELK} is available.
\<close>
locale portGraphELK =
  fixes pathToString :: "'p list \<Rightarrow> String.literal"
    and labelToString :: "'l \<Rightarrow> String.literal"
    and portSideToELK :: "'s \<Rightarrow> elk_side"
    and portLabelToString :: "'a \<Rightarrow> String.literal"
begin

definition groundPortToJSON :: "'p list \<Rightarrow> nat \<Rightarrow> ('s, 'a) port \<Rightarrow> (String.literal, int) json"
  where "groundPortToJSON prefix maxIdx p =
  OBJECT [
    (STR ''id'', STRING (pathToString prefix + portSideToString (portSideToELK (port.side p)) + String.implode (show (port.index p))))
  , (STR ''resource'', STRING (portLabelToString (port.label p)))
  , (STR ''properties'', OBJECT [
      (STR ''port.side'', STRING (portSideToString (portSideToELK (port.side p))))
    , (STR ''port.index'', NUMBER (int (if portSideToELK (port.side p) \<in> {WEST, SOUTH} then maxIdx - port.index p else port.index p)))
    ])
  , (STR ''width'', NUMBER 10)
  , (STR ''height'', NUMBER 10)
  ]"

definition nodeToJSON :: "'p list \<Rightarrow> ('s, 'a, 'p, 'l) node \<Rightarrow> (String.literal, int) json"
  where "nodeToJSON prefix n =
  OBJECT [
    (STR ''id'', STRING (pathToString (prefix @ node_name n)))
  , (STR ''width'', NUMBER 60)
  , (STR ''height'', NUMBER 60)
  , (STR ''properties'', OBJECT [
      (STR ''portConstraints'', STRING STR ''FIXED_ORDER'')
    , (STR ''nodeLabels.placement'', STRING STR ''[H_CENTER, V_CENTER, INSIDE]'')
    ])
  , (STR ''labels'', ARRAY [OBJECT [
      (STR ''text'', STRING (labelToString (node_label n)))
    , (STR ''id'', STRING (pathToString (prefix @ node_name n) + STR ''_label''))
    , (STR ''width'', NUMBER 20)
    , (STR ''height'', NUMBER 20)
    ]])
  , (STR ''ports'', ARRAY (map (\<lambda>p. groundPortToJSON (prefix @ node_name n) (length (filter (\<lambda>x. port.side x = port.side p) (node_ports n)) - 1) p) (node_ports n)))
  ]"

(*
  Not used in portToJSON because that is arrived at differently
  (the prefix there has both open prefix and the node name, which is the place name)
 *)
definition groundPlaceToID :: "'p list \<Rightarrow> ('s, 'a, 'p) place \<Rightarrow> String.literal"
  where "groundPlaceToID prefix p =
  pathToString (prefix @ place_name p) +
  portSideToString (portSideToELK (port.side (place_port p))) +
  String.implode (show (port.index (place_port p)))"

definition openPlaceToID :: "('s, 'a) port \<Rightarrow> String.literal"
  where "openPlaceToID port =
  STR ''Open'' +
  portSideToString (portSideToELK (port.side port)) +
  String.implode (show (port.index port))"

definition placeToID :: "'p list \<Rightarrow> ('s, 'a, 'p) place \<Rightarrow> String.literal"
  where "placeToID prefix p =
  ( case p of
      GroundPort _ \<Rightarrow> groundPlaceToID prefix p
    | OpenPort port \<Rightarrow> openPlaceToID port)"

definition edgeToJSON :: "'p list \<Rightarrow> ('s, 'a, 'p) edge \<Rightarrow> (String.literal, int) json"
  where "edgeToJSON prefix e =
  OBJECT [
    (STR ''id'', STRING (placeToID prefix (edge_from e) + STR ''-'' + placeToID prefix (edge_to e)))
  , (STR ''sources'', ARRAY [STRING (placeToID prefix (edge_from e))])
  , (STR ''targets'', ARRAY [STRING (placeToID prefix (edge_to e))])
  ]"

definition openPortToJSON :: "nat \<Rightarrow> ('s, 'a) port \<Rightarrow> (String.literal, int) json"
  where "openPortToJSON maxIdx p =
  OBJECT [
    (STR ''id'', STRING (openPlaceToID p))
  , (STR ''resource'', STRING (portLabelToString (port.label p)))
  , (STR ''properties'', OBJECT [
      (STR ''port.side'', STRING (portSideToString (portSideToELK (port.side p))))
    , (STR ''port.index'', NUMBER (int (if portSideToELK (port.side p) \<in> {WEST, SOUTH} then maxIdx - port.index p else port.index p)))
    ])
  , (STR ''width'', NUMBER 10)
  , (STR ''height'', NUMBER 10)
  ]"

(* Dropping edges incident on open places for now, because those would need a top-level hierarchical node to attach to *)

definition portGraphToJSON :: "'p list \<Rightarrow> ('s, 'a, 'p, 'l) port_graph \<Rightarrow> (String.literal, int) json"
  where "portGraphToJSON prefix G =
  OBJECT [
    (STR ''id'', STRING (pathToString prefix + STR ''Root''))
  , (STR ''layoutOptions'', OBJECT [
      (STR ''algorithm'', STRING STR ''layered'')
    ])
  , (STR ''children'', ARRAY (map (nodeToJSON prefix) (pg_nodes G) @
      map (\<lambda>p. openPortToJSON (length (filter (\<lambda>x. port.side x = port.side p) (pg_ports G)) - 1) p) (pg_ports G)))
  , (STR ''edges'', ARRAY (map (edgeToJSON prefix) (pg_edges G)))
  ]"

end

end
