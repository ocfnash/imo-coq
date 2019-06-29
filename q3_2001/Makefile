COQ_FLAGS = -Q . q3_2001
COQC = /Applications/CoqIDE_8.9.0.app/Contents/Resources/bin/coqc

question:		question.v misc.vo nat_list_max.vo ceil.vo inequalities.vo list_extra.vo matrices.vo
			$(COQC) $(COQ_FLAGS) question.v

matrices.vo:		matrices.v misc.vo list_extra.vo
			$(COQC) $(COQ_FLAGS) matrices.v

list_extra.vo:		list_extra.v misc.vo ceil.vo nunique.vo mode.vo value_counts.vo
			$(COQC) $(COQ_FLAGS) list_extra.v

inequalities.vo:	inequalities.v min_max_3.vo ceil.vo misc.vo
			$(COQC) $(COQ_FLAGS) inequalities.v

ceil.vo:		ceil.v misc.vo
			$(COQC) $(COQ_FLAGS) ceil.v

nat_list_max.vo:	nat_list_max.v misc.vo
			$(COQC) $(COQ_FLAGS) nat_list_max.v

misc.vo:		misc.v stdlib_candidates.vo
			$(COQC) $(COQ_FLAGS) misc.v

value_counts.vo:	value_counts.v nat_list_sum.vo
			$(COQC) $(COQ_FLAGS) value_counts.v

mode.vo:		mode.v misc.vo largest_elt.vo
			$(COQC) $(COQ_FLAGS) mode.v

nunique.vo:		nunique.v misc.vo
			$(COQC) $(COQ_FLAGS) nunique.v

min_max_3.vo:		min_max_3.v
			$(COQC) $(COQ_FLAGS) min_max_3.v

stdlib_candidates.vo:	stdlib_candidates.v
			$(COQC) $(COQ_FLAGS) stdlib_candidates.v

nat_list_sum.vo:	nat_list_sum.v
			$(COQC) $(COQ_FLAGS) nat_list_sum.v

largest_elt.vo:		largest_elt.v ceil.vo misc.vo nat_list_sum.vo
			$(COQC) $(COQ_FLAGS) largest_elt.v

clean:
		rm -rf *.glob *.vo *.o *.hi .*.aux
