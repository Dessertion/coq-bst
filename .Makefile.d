CpdtTactics.vo CpdtTactics.glob CpdtTactics.v.beautified CpdtTactics.required_vo: CpdtTactics.v 
CpdtTactics.vos CpdtTactics.vok CpdtTactics.required_vos: CpdtTactics.v 
Frap/Sets.vo Frap/Sets.glob Frap/Sets.v.beautified Frap/Sets.required_vo: Frap/Sets.v 
Frap/Sets.vos Frap/Sets.vok Frap/Sets.required_vos: Frap/Sets.v 
Frap/Map.vo Frap/Map.glob Frap/Map.v.beautified Frap/Map.required_vo: Frap/Map.v Frap/Sets.vo
Frap/Map.vos Frap/Map.vok Frap/Map.required_vos: Frap/Map.v Frap/Sets.vos
Frap/Var.vo Frap/Var.glob Frap/Var.v.beautified Frap/Var.required_vo: Frap/Var.v 
Frap/Var.vos Frap/Var.vok Frap/Var.required_vos: Frap/Var.v 
Frap/Relations.vo Frap/Relations.glob Frap/Relations.v.beautified Frap/Relations.required_vo: Frap/Relations.v 
Frap/Relations.vos Frap/Relations.vok Frap/Relations.required_vos: Frap/Relations.v 
Frap/Invariant.vo Frap/Invariant.glob Frap/Invariant.v.beautified Frap/Invariant.required_vo: Frap/Invariant.v Frap/Relations.vo
Frap/Invariant.vos Frap/Invariant.vok Frap/Invariant.required_vos: Frap/Invariant.v Frap/Relations.vos
Frap/ModelCheck.vo Frap/ModelCheck.glob Frap/ModelCheck.v.beautified Frap/ModelCheck.required_vo: Frap/ModelCheck.v Frap/Invariant.vo Frap/Relations.vo Frap/Sets.vo
Frap/ModelCheck.vos Frap/ModelCheck.vok Frap/ModelCheck.required_vos: Frap/ModelCheck.v Frap/Invariant.vos Frap/Relations.vos Frap/Sets.vos
Frap/FrapWithoutSets.vo Frap/FrapWithoutSets.glob Frap/FrapWithoutSets.v.beautified Frap/FrapWithoutSets.required_vo: Frap/FrapWithoutSets.v Frap/Sets.vo Frap/Relations.vo Frap/Map.vo Frap/Var.vo Frap/Invariant.vo Frap/ModelCheck.vo
Frap/FrapWithoutSets.vos Frap/FrapWithoutSets.vok Frap/FrapWithoutSets.required_vos: Frap/FrapWithoutSets.v Frap/Sets.vos Frap/Relations.vos Frap/Map.vos Frap/Var.vos Frap/Invariant.vos Frap/ModelCheck.vos
Frap/Frap.vo Frap/Frap.glob Frap/Frap.v.beautified Frap/Frap.required_vo: Frap/Frap.v Frap/FrapWithoutSets.vo
Frap/Frap.vos Frap/Frap.vok Frap/Frap.required_vos: Frap/Frap.v Frap/FrapWithoutSets.vos
Frap/SepCancel.vo Frap/SepCancel.glob Frap/SepCancel.v.beautified Frap/SepCancel.required_vo: Frap/SepCancel.v Frap/Frap.vo
Frap/SepCancel.vos Frap/SepCancel.vok Frap/SepCancel.required_vos: Frap/SepCancel.v Frap/Frap.vos
Util.vo Util.glob Util.v.beautified Util.required_vo: Util.v CpdtTactics.vo Frap/Frap.vo
Util.vos Util.vok Util.required_vos: Util.v CpdtTactics.vos Frap/Frap.vos
AVL.vo AVL.glob AVL.v.beautified AVL.required_vo: AVL.v Frap/Frap.vo CpdtTactics.vo Util.vo
AVL.vos AVL.vok AVL.required_vos: AVL.v Frap/Frap.vos CpdtTactics.vos Util.vos
