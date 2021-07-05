-- Signatures

sig Account {
	pipelines : set Pipeline,
	researchers : set Researcher
}

sig Researcher {} { this in Account.researchers }

sig Pipeline {
	stages : set Stage
} { this in Account.pipelines }

sig Stage {
	input : one Format,
	output : one Format,
	next : lone Stage
} { this in Pipeline.stages }

abstract sig Format {}
one sig JSON, JPEG, TIFF, TXT extends Format {}


-- Predicates

pred is_initial_stage(s : Stage) {
	no s.~next
}

pred is_final_stage(s : Stage) {
	no s.next
}

pred connected(s, s' : Stage) {
	s in s'.*next or s' in s.*next
}

pred same_pipeline (s, s' : Pipeline.stages) {
	some p : Pipeline | s in p.stages and s' in p.stages
}


-- Facts

fact input_match_output {
	all s, s' : Stage |
		s.next = s' implies s.output = s'.input
}

fact initial_stage_format_must_be_json {
	all s : Stage |
		is_initial_stage[s] implies s.input = JSON
}

fact final_stage_format_must_be_jpeg {
	all s : Stage |
		is_final_stage[s] implies s.output = JPEG
}

fact no_shared_stage_between_pipelines {
	all disj p, p' : Pipeline | no p.stages & p'.stages
}

fact unique_initial_stage_per_pipeline {
	all p : Pipeline | lone s : p.stages |
		is_initial_stage[s]
}

fact next_stage_belongs_to_the_same_pipeline {
	all p : Pipeline, s : Stage |
		s in p.stages implies s.next in p.stages
}

fact no_cyclic_pipeline {
	no s : Stage | s in s.^next
}


-- Checks

check no_orphan_pipeline {
	all p : Pipeline | some a : Account |
		p in a.pipelines
}

check no_orphan_researcher {
	all r : Researcher | some a : Account |
		r in a.researchers
}

check no_orphan_stage {
	all s : Stage | some p : Pipeline |
		s in p.stages
}

check connectivity_is_commutative {
	all s, s' : Stage |
		connected[s, s'] iff connected[s', s]
}

check connectivity_is_reflexive {
	all s : Stage | connected[s, s]
}

check same_pipeline_is_commutative {
	all s, s' : Pipeline.stages | same_pipeline[s, s'] iff same_pipeline[s', s]
}

check same_pipeline_is_reflexive {
	all s : Pipeline.stages | same_pipeline[s, s]
}

check stages_are_connected_iff_belongs_to_the_same_pipeline {
	all s, s' : Pipeline.stages |
		connected[s, s'] iff same_pipeline[s, s']
}

check unique_predecessor_for_stage {
	all s : Stage | lone s.~next
}

check unicity_of_initial_stage_on_pipeline {
	all p : Pipeline | lone s : p.stages | is_initial_stage[s]
}

check unicity_of_final_stage_on_pipeline {
	all p : Pipeline | lone s : p.stages | is_final_stage[s]
}

check every_nonempty_pipeline_has_initial_and_final_stage {
	all p : Pipeline |
		some p.stages implies {
			one i : p.stages | is_initial_stage[i]
			one f : p.stages | is_final_stage[f]
		}
}


-- Valid instances

pred empty_pipeline(p : Pipeline) {
	no p.stages
}
run empty_pipeline for 5


-- Shows

pred show_specific() {
	#Account = 1
	#Researcher = 2
	#Pipeline =3
}
run show_specific for 10 but exactly 10 Stage

pred show() {}
run show for 5
