instance.vo instance.glob instance.v.beautified instance.required_vo: instance.v 
instance.vio: instance.v 
instance.vos instance.vok instance.required_vos: instance.v 
Lemma.vo Lemma.glob Lemma.v.beautified Lemma.required_vo: Lemma.v PF.vo
Lemma.vio: Lemma.v PF.vio
Lemma.vos Lemma.vok Lemma.required_vos: Lemma.v PF.vos
PF.vo PF.glob PF.v.beautified PF.required_vo: PF.v 
PF.vio: PF.v 
PF.vos PF.vok PF.required_vos: PF.v 
proj1.vo proj1.glob proj1.v.beautified proj1.required_vo: proj1.v PF.vo
proj1.vio: proj1.v PF.vio
proj1.vos proj1.vok proj1.required_vos: proj1.v PF.vos
proj2.vo proj2.glob proj2.v.beautified proj2.required_vo: proj2.v Lemma.vo PF.vo
proj2.vio: proj2.v Lemma.vio PF.vio
proj2.vos proj2.vok proj2.required_vos: proj2.v Lemma.vos PF.vos
