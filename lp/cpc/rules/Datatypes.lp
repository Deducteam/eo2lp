require open cpc.Core Stdlib.Set cpc.theories.Datatypes cpc.programs.Datatypes;
sequential symbol !mk_dt_split [D : Set]: τ (eo⋅⋅List ⤳ D ⤳ Bool);
rule !mk_dt_split eo⋅⋅List⋅⋅nil ($x) ↪ false
with !mk_dt_split (eo⋅⋅List⋅⋅cons ($c) ($xs)) ($x) ↪ eo⋅⋅cons or (is ($c) ($x)) (!mk_dt_split ($xs) ($x));
sequential symbol !mk_dt_inst_rec [D : Set] [T : Set]: τ (eo⋅⋅List ⤳ D ⤳ T ⤳ D);
rule !mk_dt_inst_rec eo⋅⋅List⋅⋅nil ($x) ($tb) ↪ $tb
with !mk_dt_inst_rec (eo⋅⋅List⋅⋅cons ($s) ($xs)) ($x) ($t) ↪ !mk_dt_inst_rec ($xs) ($x) ($t ($s ($x)));
sequential symbol !mk_dt_inst_tuple_rec [D : Set] [U : Set]: τ ((eo⋅⋅quote U) ⤳ D ⤳ Int ⤳ U);
rule !mk_dt_inst_tuple_rec UnitTuple ($x) ($n) ↪ tuple⋅unit
with !mk_dt_inst_tuple_rec (Tuple ($T1) ($T2)) ($x) ($n) ↪ eo⋅⋅cons tuple (tuple⋅select ($n) ($x)) (!mk_dt_inst_tuple_rec ($T2) ($x) (eo⋅⋅add ($n) (1)));
sequential symbol !mk_dt_inst [C : Set] [D : Set]: τ (eo⋅⋅Type ⤳ C ⤳ D ⤳ D);
rule !mk_dt_inst (Tuple ($T1) ($T2)) tuple ($xt) ↪ !mk_dt_inst_tuple_rec (Tuple ($T1) ($T2)) ($xt) (0)
with !mk_dt_inst UnitTuple tuple⋅unit ($xu) ↪ tuple⋅unit
with !mk_dt_inst ($D) ($c) ($x) ↪ !mk_dt_inst_rec (!dt_get_selectors ($D) ($c)) ($x) (!dt_inst_cons_of ($D) ($c));
sequential symbol !mk_dt_cons_eq [T : Set]: τ (T ⤳ T ⤳ Bool);
rule !mk_dt_cons_eq (tuple ($a) {|as|}) (tuple ($b) ($bs)) ↪ eo⋅⋅cons and (and (= ($a) ($b))) (!mk_dt_cons_eq {|as|} ($bs))
with !mk_dt_cons_eq ($f ($a)) ($g ($b)) ↪ eo⋅⋅list_concat and (!mk_dt_cons_eq ($f) ($g)) (and (and (= ($a) ($b))))
with !mk_dt_cons_eq ($c) ($c) ↪ true;
sequential symbol !dt_find_cycle_rec [T : Set]: τ (T ⤳ {|@List|} ⤳ {|@List|} ⤳ Bool);
rule !dt_find_cycle_rec ($f ($a)) ($s) ($l) ↪ !dt_find_cycle_rec ($f) ($s) (eo⋅⋅cons {|@list|} ($a) ($l))
with !dt_find_cycle_rec ($c) ($s) ($l) ↪ eo⋅⋅ite (!dt_is_cons ($c)) (!dt_find_cycle_list ($l) ($s)) false;
symbol !dt_find_cycle [T : Set] (t : τ T) (s : τ {|@List|})≔ !dt_find_cycle_rec t s {|@list.nil|};
sequential symbol !dt_find_cycle_list : τ ({|@List|} ⤳ {|@List|} ⤳ Bool);
rule !dt_find_cycle_list ({|@list|} ($s) ($ts)) ({|@list|} ($s)) ↪ true
with !dt_find_cycle_list ({|@list|} ($t) ($ts)) ($ss) ↪ eo⋅⋅ite (!dt_find_cycle ($t) ($ss)) true (!dt_find_cycle_list ($ts) ($ss))
with !dt_find_cycle_list {|@list.nil|} ($ss) ↪ false;
sequential symbol !dt_collapse_updater_rhs [U : Set] [T : Set]: τ (U ⤳ T ⤳ Int ⤳ U);
rule !dt_collapse_updater_rhs ($f ($x)) ($a) (0) ↪ $f ($a)
with !dt_collapse_updater_rhs ($f ($x)) ($a) ($n) ↪ !dt_collapse_updater_rhs ($f) ($a) (eo⋅⋅add ($n) (-1)) ($x);
sequential symbol !tuple_collapse_updater_rhs [U : Set] [T : Set]: τ (U ⤳ T ⤳ Int ⤳ U);
rule !tuple_collapse_updater_rhs (tuple ($b) ($ts)) ($a) (0) ↪ tuple ($a) ($ts)
with !tuple_collapse_updater_rhs (tuple ($b) ($ts)) ($a) ($n) ↪ eo⋅⋅cons tuple ($b) (!tuple_collapse_updater_rhs ($ts) ($a) (eo⋅⋅add ($n) (-1)))
with !tuple_collapse_updater_rhs tuple⋅unit ($a) ($n) ↪ tuple⋅unit;
sequential symbol !mk_dt_collapse_updater_rhs [D : Set]: τ (D ⤳ D);
rule !mk_dt_collapse_updater_rhs (update ($s) ($t) ($a)) ↪ (let ss ≔ !dt_get_selectors_of_app (eo⋅⋅typeof ($t)) ($t) in (let index ≔ eo⋅⋅list_find eo⋅⋅List⋅⋅cons ss ($s) in eo⋅⋅ite (eo⋅⋅is_neg index) ($t) (!dt_collapse_updater_rhs ($t) ($a) (eo⋅⋅add (eo⋅⋅len ss) index (-1)))))
with !mk_dt_collapse_updater_rhs (tuple⋅update ($n) ($t) ($a)) ↪ !tuple_collapse_updater_rhs ($t) ($a) ($n);
sequential symbol !dt_updater_elim_rhs [D : Set] [X : Set]: τ (D ⤳ eo⋅⋅List ⤳ X ⤳ D);
rule !dt_updater_elim_rhs (update ($s) ($t) ($a)) (eo⋅⋅List⋅⋅cons ($s) ($ss)) ($c) ↪ !dt_updater_elim_rhs (update ($s) ($t) ($a)) ($ss) ($c ($a))
with !dt_updater_elim_rhs (update ($s) ($t) ($a)) (eo⋅⋅List⋅⋅cons ($s1) ($ss)) ($c) ↪ !dt_updater_elim_rhs (update ($s) ($t) ($a)) ($ss) ($c ($s1 ($t)))
with !dt_updater_elim_rhs (update ($s) ($t) ($a)) eo⋅⋅List⋅⋅nil ($cd) ↪ $cd;
sequential symbol !tuple_updater_elim_rhs [D : Set]: τ (D ⤳ eo⋅⋅List ⤳ D);
rule !tuple_updater_elim_rhs (tuple⋅update ($n) ($t) ($a)) (eo⋅⋅List⋅⋅cons (tuple⋅select ($n)) ($ss)) ↪ eo⋅⋅cons tuple ($a) (!tuple_updater_elim_rhs (tuple⋅update ($n) ($t) ($a)) ($ss))
with !tuple_updater_elim_rhs (tuple⋅update ($n) ($t) ($a)) (eo⋅⋅List⋅⋅cons ($s) ($ss)) ↪ eo⋅⋅cons tuple ($s ($t)) (!tuple_updater_elim_rhs (tuple⋅update ($n) ($t) ($a)) ($ss))
with !tuple_updater_elim_rhs (tuple⋅update ($n) ($tu) ($a)) eo⋅⋅List⋅⋅nil ↪ tuple⋅unit;
sequential symbol !mk_dt_updater_elim_rhs [D : Set] [U : Set]: τ (D ⤳ U ⤳ eo⋅⋅List ⤳ D);
rule !mk_dt_updater_elim_rhs (update ($s) ($t) ($a)) ($c) ($ss) ↪ !dt_updater_elim_rhs (update ($s) ($t) ($a)) ($ss) (!dt_inst_cons_of (eo⋅⋅typeof ($t)) ($c))
with !mk_dt_updater_elim_rhs (tuple⋅update ($n) ($t) ($a)) tuple ($ss) ↪ !tuple_updater_elim_rhs (tuple⋅update ($n) ($t) ($a)) ($ss);
