#include "edusat.h"


Solver S;

using namespace std;

inline bool verbose_now() {
	return verbose > 1;
}




/******************  Reading the CNF ******************************/
#pragma region readCNF
void skipLine(ifstream& in) {
	for (;;) {
		//if (in.get() == EOF || in.get() == '\0') return;
		if (in.get() == '\n') { return; }
	}
}

static void skipWhitespace(ifstream& in, char&c) {
	c = in.get();
	while ((c >= 9 && c <= 13) || c == 32)
		c = in.get();
}

static int parseInt(ifstream& in) {
	int     val = 0;
	bool    neg = false;
	char c;
	skipWhitespace(in, c);
	if (c == '-') neg = true, c = in.get();
	if (c < '0' || c > '9') cout << c, Abort("Unexpected char in input", 1);
	while (c >= '0' && c <= '9')
		val = val * 10 + (c - '0'),
		c = in.get();
	return neg ? -val : val;
}

void Solver::read_cnf(ifstream& in) {
	int i;
	unsigned int vars, clauses, unary = 0;
	set<Lit> s;
	Clause c;


	while (in.peek() == 'c') skipLine(in);

	if (!match(in, "p cnf")) Abort("Expecting `p cnf' in the beginning of the input file", 1);
	in >> vars; // since vars is int, it reads int from the stream.
	in >> clauses;
	if (!vars || !clauses) Abort("Expecting non-zero variables and clauses", 1);
	cout << "vars: " << vars << " clauses: " << clauses << endl;
	cnf.reserve(clauses);

	set_nvars(vars);
	set_nclauses(clauses);
	initialize();

	while (in.good() && in.peek() != EOF) {
		i = parseInt(in);
		if (i == 0) {
			c.cl().resize(s.size());
			copy(s.begin(), s.end(), c.cl().begin());
			switch (c.size()) {
			case 0: {
				stringstream num;  // this allows to convert int to string
				num << cnf_size() + 1; // converting int to string.
				Abort("Empty clause not allowed in input formula (clause " + num.str() + ")", 1); // concatenating strings
			}
			case 1: {
				Lit l = c.cl()[0];
				// checking if we have conflicting unaries. Sufficiently rare to check it here rather than 
				// add a check in BCP. 
				if (state[l2v(l)] != VarState::V_UNASSIGNED)
					if (Neg(l) != (state[l2v(l)] == VarState::V_FALSE)) {
						S.print_stats();
						Abort("UNSAT (conflicting unaries for var " + to_string(l2v(l)) +")", 0);
					}
				assert_lit(l);
				add_unary_clause(l);
				break; // unary clause. Note we do not add it as a clause. 
			}
			default: add_clause(c, 0, 1);
			}
			c.reset();
			s.clear();
			continue;
		}
		if (Abs(i) > vars) Abort("Literal index larger than declared on the first line", 1);
		if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(abs(i));
		i = v2l(i);		
		if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(i);
		s.insert(i);
	}	
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) reset_iterators();
	cout << "Read " << cnf_size() << " clauses in " << cpuTime() - begin_time << " secs." << endl << "Solving..." << endl;
}

#pragma endregion readCNF

/******************  Solving ******************************/
#pragma region solving
void Solver::reset() { // invoked initially + every restart
	dl = 0;
	max_dl = 0;
	conflicting_clause_idx = -1;	
	separators.push_back(0); // we want separators[1] to match dl=1. separators[0] is not used.
	conflicts_at_dl.push_back(0);
}


inline void Solver::reset_iterators(double where) {
	m_Score2Vars_it = (where == 0) ? m_Score2Vars.begin() : m_Score2Vars.lower_bound(where);
	Assert(m_Score2Vars_it != m_Score2Vars.end());
	m_VarsSameScore_it = m_Score2Vars_it->second.begin();
	m_should_reset_iterators = false;
}

void Solver::initialize() {	
	
	state.resize(nvars + 1, VarState::V_UNASSIGNED);
	prev_state.resize(nvars + 1, VarState::V_FALSE); // we set initial assignment with phase-saving to false. 
	antecedent.resize(nvars + 1, -1);	
	marked.resize(nvars+1);
	dlevel.resize(nvars+1);
	
	nlits = 2 * nvars;
	watches.resize(nlits + 1);
	LitScore.resize(nlits + 1);
	//initialize scores 	
	m_activity.resize(nvars + 1);	
	m_curr_activity = 0.0f;
	for (unsigned int v = 0; v <= nvars; ++v) {			
		m_activity[v] = 0;		
	}
	reset();
}

inline void Solver::assert_lit(Lit l) {
	trail.push_back(l);
	int var = l2v(l);
	if (Neg(l)) prev_state[var] = state[var] = VarState::V_FALSE; else prev_state[var] = state[var] = VarState::V_TRUE;
	dlevel[var] = dl;
	++num_assignments;
	if (verbose_now()) cout << l2rl(l) <<  " @ " << dl << endl;
}

void Solver::m_rescaleScores(double& new_score) {
	if (verbose_now()) cout << "Rescale" << endl;
	new_score /= Rescale_threshold;
	for (unsigned int i = 1; i <= nvars; i++)
		m_activity[i] /= Rescale_threshold;
	m_var_inc /= Rescale_threshold;
	// rebuilding the scaled-down m_Score2Vars.
	map<double, unordered_set<Var>, greater<double>> tmp_map;
	double prev_score = 0.0f;
	for (auto m : m_Score2Vars) {
		double scaled_score = m.first / Rescale_threshold;
		if (scaled_score == prev_score) // This can happen due to rounding
			tmp_map[scaled_score].insert(m_Score2Vars[m.first].begin(), m_Score2Vars[m.first].end());
		else
			tmp_map[scaled_score] = m_Score2Vars[m.first];
		prev_score = scaled_score;
	}
	tmp_map.swap(m_Score2Vars);
}

void Solver::bumpVarScore(int var_idx) {
	double new_score;
	double score = m_activity[var_idx];		

	if (score > 0) {
		Assert(m_Score2Vars.find(score) != m_Score2Vars.end());
		m_Score2Vars[score].erase(var_idx);
		if (m_Score2Vars[score].size() == 0) m_Score2Vars.erase(score);
	}
	new_score = score + m_var_inc;
	m_activity[var_idx] = new_score;

	// Rescaling, to avoid overflows; 
	if (new_score > Rescale_threshold) {
		m_rescaleScores(new_score);
	}

	if (m_Score2Vars.find(new_score) != m_Score2Vars.end())
		m_Score2Vars[new_score].insert(var_idx);
	else
		m_Score2Vars[new_score] = unordered_set<int>({ var_idx });
}

void Solver::bumpLitScore(int lit_idx) {
	LitScore[lit_idx]++;
}

void Solver::add_clause(Clause& c, int l, int r) {	
	Assert(c.size() > 1) ;
	c.lw_set(l);
	c.rw_set(r);
	int loc = static_cast<int>(cnf.size());  // the first is in location 0 in cnf	
	int size = c.size();
	
	watches[c.lit(l)].push_back(loc); 
	watches[c.lit(r)].push_back(loc);
	cnf.push_back(c);
}

void Solver::add_unary_clause(Lit l) {		
	unaries.push_back(l);
}

int Solver :: getVal(Var v) {
	// ValDecHeuristic : Heuristic to choose value
	switch (ValDecHeuristic) {
	case VAL_DEC_HEURISTIC::PHASESAVING: {
		VarState saved_phase = prev_state[v];		
		switch (saved_phase) {
		case VarState::V_FALSE:	return v2l(-v);
		case VarState::V_TRUE: return v2l(v);
		default: Assert(0);
		}
	}
	case VAL_DEC_HEURISTIC::LITSCORE:
	{
		int litp = v2l(v), litn = v2l(-v);
		int pScore = LitScore[litp], nScore = LitScore[litn];
		return pScore > nScore ? litp : litn;
	}
	default: Assert(0);
	}	
	return 0;
}

SolverState Solver::decide(){
	if (verbose_now()) cout << "decide" << endl;
	Lit best_lit = 0;	
	int max_score = 0;
	Var bestVar = 0;
	switch (VarDecHeuristic) {

	case  VAR_DEC_HEURISTIC::MINISAT: {
		// m_Score2Vars_r_it and m_VarsSameScore_it are fields. 
		// When we get here they are the location where we need to start looking. 		
		if (m_should_reset_iterators) reset_iterators(m_curr_activity);
		Var v = 0;
		int cnt = 0;
		if (m_Score2Vars_it == m_Score2Vars.end()) break;
		while (true) { // scores from high to low
			while (m_VarsSameScore_it != m_Score2Vars_it->second.end()) {
				v = *m_VarsSameScore_it;
				++m_VarsSameScore_it;
				++cnt;
				if (state[v] == VarState::V_UNASSIGNED) { // found a var to assign
					m_curr_activity = m_Score2Vars_it->first;
					assert(m_curr_activity == m_activity[v]);
					best_lit = getVal(v); // decide chose a variable but we need to assign value to this variable, getval assigns value to the variable					
					goto Apply_decision;
				}
			}
			++m_Score2Vars_it;
			if (m_Score2Vars_it == m_Score2Vars.end()) break;
			m_VarsSameScore_it = m_Score2Vars_it->second.begin();
		}
		break;
	}
	default: Assert(0);
	}	
		
	assert(!best_lit);
	S.print_state(Assignment_file);
	return SolverState::SAT;


Apply_decision:	// label
	dl++; // increase decision level
	if (dl > max_dl) {
		max_dl = dl;
		separators.push_back(trail.size());
		conflicts_at_dl.push_back(num_learned);
	}
	else {
		separators[dl] = trail.size();
		conflicts_at_dl[dl] = num_learned;
	}
	
	assert_lit(best_lit); // assigns the value to the variable
	++num_decisions;	
	return SolverState::UNDEF;
}

inline ClauseState Clause::next_not_false(bool is_left_watch, Lit other_watch, bool binary, int& loc) {  
	if (verbose_now()) cout << "next_not_false" << endl;
	
	if (!binary)
		for (vector<int>::iterator it = c.begin(); it != c.end(); ++it) {
			LitState LitState = S.lit_state(*it);
			if (LitState != LitState::L_UNSAT && *it != other_watch) { // found another watch_lit
				loc = distance(c.begin(), it);
				if (is_left_watch) lw = loc;    // if literal was the left one 
				else rw = loc;				
				return ClauseState::C_UNDEF;
			}
		}
	switch (S.lit_state(other_watch)) {
	case LitState::L_UNSAT: // conflict
		if (verbose_now()) { print_real_lits(); cout << " is conflicting" << endl; }
		return ClauseState::C_UNSAT;
	case LitState::L_UNASSIGNED: return ClauseState::C_UNIT; // unit clause. Should assert the other watch_lit.	
	case LitState::L_SAT: return ClauseState::C_SAT; // other literal is satisfied. 
	default: Assert(0); return ClauseState::C_UNDEF; // just to supress warning. 
	}
}

void Solver::test() { // tests that each clause is watched twice. 	
	for (unsigned int idx = 0; idx < cnf.size(); ++idx) {
		Clause c = cnf[idx];
		bool found = false;
		for (int zo = 0; zo <= 1; ++zo) {
			for (vector<int>::iterator it = watches[c.cl()[zo]].begin(); !found && it != watches[c.cl()[zo]].end(); ++it) {				
				if (*it == idx) {
					found = true;
					break;
				}
			}
		}
		if (!found) {
			cout << "idx = " << idx << endl;
			c.print();
			cout << endl;
			cout << c.size();
		}
		Assert(found);
	}
}
//TODO: increase the score of variables of learnt clauses that were propagated by clauses of LBD 2
SolverState Solver::BCP() {
	if (verbose_now()) cout << "BCP" << endl;
	if (verbose_now()) cout << "qhead = " << qhead << " trail-size = " << trail.size() << endl;
	// qhead = pointer into trail that points to the last literal that is still not handled 
	// BCP starts from last decision level from last literal that is still not handled
	while (qhead < trail.size()) { 
		Lit NegatedLit = negate(trail[qhead++]); // in trail we save literal itself, in BCP 
		Assert(lit_state(NegatedLit) == LitState::L_UNSAT);
		if (verbose_now()) cout << "propagating " << l2rl(negate(NegatedLit)) << endl;
		vector<int> new_watch_list; // The original watch list minus those clauses that changed a watch. The order is maintained. 
		int new_watch_list_idx = watches[NegatedLit].size() - 1; // Since we are traversing the watch_list backwards, this index goes down.
		new_watch_list.resize(watches[NegatedLit].size());
		// traverse all clauses that are pointed to by literal NegatedLit
		for (vector<int>::reverse_iterator it = watches[NegatedLit].rbegin(); it != watches[NegatedLit].rend() && conflicting_clause_idx < 0; ++it) {
			Clause& c = cnf[*it];
			Lit l_watch = c.get_lw_lit(), 
				r_watch = c.get_rw_lit();			
			bool binary = c.size() == 2;
			bool is_left_watch = (l_watch == NegatedLit);
			Lit other_watch = is_left_watch? r_watch: l_watch;
			int NewWatchLocation;
			ClauseState res = c.next_not_false(is_left_watch, other_watch, binary, NewWatchLocation);
			if (res != ClauseState::C_UNDEF) new_watch_list[new_watch_list_idx--] = *it; //in all cases but the move-watch_lit case we leave watch_lit where it is
			switch (res) {
			case ClauseState::C_UNSAT: { // conflict				
				if (verbose_now()) print_state();
				if (dl == 0) return SolverState::UNSAT;				
				conflicting_clause_idx = *it;  // this will also break the loop
				 int dist = distance(it, watches[NegatedLit].rend()) - 1; // # of entries in watches[NegatedLit] that were not yet processed when we hit this conflict. 
				// Copying the remaining watched clauses:
				for (int i = dist - 1; i >= 0; i--) {
					new_watch_list[new_watch_list_idx--] = watches[NegatedLit][i];
				}
				if (verbose_now()) cout << "conflict" << endl;
				break;
			}
			case ClauseState::C_SAT: 
				if (verbose_now()) cout << "clause is sat" << endl;
				break; // nothing to do when clause has a satisfied literal.
			case ClauseState::C_UNIT: { // new implication				
				if (verbose_now()) cout << "propagating: ";
				assert_lit(other_watch);
				antecedent[l2v(other_watch)] = *it;
				if (verbose_now()) cout << "new implication <- " << l2rl(other_watch) << endl;
				// when a learnt clause is used in unit propagation, recalculate its LBD score and update it.
				// CLause = c
				int new_lbd_score = LBD_score_calculation(c.cl());
				lbd_score_map[c.cl()] = new_lbd_score;
				break;
			}
			default: // replacing watch_lit
				Assert(NewWatchLocation < static_cast<int>(c.size()));
				int new_lit = c.lit(NewWatchLocation);
				watches[new_lit].push_back(*it);
				if (verbose_now()) { c.print_real_lits(); cout << " now watched by " << l2rl(new_lit) << endl;}
			}
		}
		// resetting the list of clauses watched by this literal.
		watches[NegatedLit].clear();
		new_watch_list_idx++; // just because of the redundant '--' at the end. 		
		watches[NegatedLit].insert(watches[NegatedLit].begin(), new_watch_list.begin() + new_watch_list_idx, new_watch_list.end());

		//print_watches();
		if (conflicting_clause_idx >= 0) return SolverState::CONFLICT;
		new_watch_list.clear();
	}
	return SolverState::UNDEF;
}


/*******************************************************************************************************************
name: analyze
input:	1) conflicting clause
		2) dlevel
		3) marked
		
assumes: 1) no clause should have the same literal twice. To guarantee this we read through a set in read_cnf. 
            Wihtout this assumption it may loop forever because we may remove only one copy of the pivot.

This is Alg. 1 from "HaifaSat: a SAT solver based on an Abstraction/Refinement model" 
********************************************************************************************************************/

int Solver::analyze(const Clause conflicting) {
	if (verbose_now()) cout << "analyze" << endl;
	Clause	current_clause = conflicting, 
			new_clause;
	int resolve_num = 0,
		bktrk = 0, 
		watch_lit = 0, // points to what literal in the learnt clause should be watched, other than the asserting one
		antecedents_idx = 0;

	Lit u;
	Var v;
	trail_t::reverse_iterator t_it = trail.rbegin();
	do {
		for (clause_it it = current_clause.cl().begin(); it != current_clause.cl().end(); ++it) {
			Lit lit = *it;
			v = l2v(lit);
			if (!marked[v]) {
				marked[v] = true;
				if (dlevel[v] == dl) ++resolve_num;
				else { // literals from previos decision levels (roots) are entered to the learned clause.
					new_clause.insert(lit);
					if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) bumpVarScore(v);
					if (ValDecHeuristic == VAL_DEC_HEURISTIC::LITSCORE) bumpLitScore(lit);
					int c_dl = dlevel[v];
					if (c_dl > bktrk) {
						bktrk = c_dl;
						watch_lit = new_clause.size() - 1;
					}
				}
			}
		} 
		
		while (t_it != trail.rend()) {
			u = *t_it;
			v = l2v(u);
			++t_it;
			if (marked[v]) break;
		}
		marked[v] = false;
		--resolve_num;
		if(!resolve_num) continue; 
		int ant = antecedent[v];		
		current_clause = cnf[ant]; 
		current_clause.cl().erase(find(current_clause.cl().begin(), current_clause.cl().end(), u));	
	}	while (resolve_num > 0);
	for (clause_it it = new_clause.cl().begin(); it != new_clause.cl().end(); ++it) 
		marked[l2v(*it)] = false;
	Lit Negated_u = negate(u);
	new_clause.cl().push_back(Negated_u);		
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) 
		m_var_inc *= 1 / var_decay; // increasing importance of participating variables.
	
	++num_learned;
	asserted_lit = Negated_u;
	if (new_clause.size() == 1) { // unary clause	
		add_unary_clause(Negated_u);
	}
	else {
		add_clause(new_clause, watch_lit, new_clause.size() - 1);
	}

	int lbd_score = LBD_score_calculation(new_clause.cl());	
	lbd_score_map.insert(pair<clause_t, int>(new_clause.cl(), lbd_score));
	double activity_score = clause_activity_calculation(new_clause.cl());
	activity_score_map.insert(pair<clause_t, double>(new_clause.cl(), activity_score));
	double score = clause_score_calculation(new_clause.cl());
	score_map.insert(pair<clause_t, double>(new_clause.cl(), score));

	if (verbose_now()) {	
		cout << "Learned clause #" << cnf_size() + unaries.size() << ". "; 
		new_clause.print_real_lits(); 
		cout << endl;
		cout << " learnt clauses:  " << num_learned;				
		cout << " Backtracking to level " << bktrk << endl;
	}

	if (verbose >= 1 && !(num_learned % 1000)) {
		cout << "Learned: "<< num_learned <<" clauses" << endl;		
	}	
	return bktrk; 
}

int Solver::LBD_score_calculation(clause_t clause) {
	set<Lit> dist_levels;
	for (clause_it it = clause.begin(); it != clause.end(); ++it) {
		Var v = l2v(*it);
		dist_levels.insert(dlevel[v]);
	}
	return dist_levels.size();
}
/* clause activity = sum of variables activity*/
double Solver::clause_activity_calculation(clause_t clause) { 
	double activity = 0.0;
	for (clause_it it = clause.begin(); it != clause.end(); ++it) {
		Var v = l2v(*it);
		activity += m_activity[v];
	}
	return activity;
}

double Solver::clause_score_calculation(clause_t clause) {
	double score = 0.0;
	int lbd_score = lbd_score_map[clause];
	double activity_score = activity_score_map[clause];
	score = 0.7 * lbd_score + 0.3*activity_score;
	return score;
}

/// <summary>
/// 
/// </summary>
/// <param name="k"></param>
void Solver::backtrack(int k) {
	if (verbose_now()) cout << "backtrack" << endl;
	// local restart means that we restart if the number of conflicts learned in this 
	// decision level has passed the threshold. 
	if (k > 0 && (num_learned - conflicts_at_dl[k] > restart_threshold)) {	// "local restart"	
		         // learned clauses - number of learned clauses at decision level k = effort done in this subtree
		restart(); 		
		return;
	}
	// restart: erase the trail from level 1 and up. as if we are restarting solver all over again
	// but we are not actually restarting solver all over again because we still have everything that we learnt and all the scores
	// basically it is to backtrack to level 1
	// level 0 -> true without any connection to all decisions made, that's why we do not delete them.
	// local restart: criterion that decides when to do a restart.
	// idea: after each decision, solver does a lot of work, when we backtrack to that decision we check how much work was invested in this sub-tree
	// if there is a lot of work we restart because chances are there is no solution in this way.

	static int counter = 0;
		
	for (trail_t::iterator it = trail.begin() + separators[k+1]; it != trail.end(); ++it) { // erasing from k+1
		// separators[k+1] -> index into trail , trail.begin() + separators[k+1]-> place in trail where decision level k+1 starts
		Var v = l2v(*it); //*it = literal
		if (dlevel[v]) { // we need the condition because of learnt unary clauses. In that case we enforce an assignment with dlevel = 0.
			state[v] = VarState::V_UNASSIGNED;
			if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_curr_activity = max(m_curr_activity, m_activity[v]);
		}
	}
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) m_should_reset_iterators = true;
	if (verbose_now()) print_state();
	trail.erase(trail.begin() + separators[k+1], trail.end());
	qhead = trail.size();
	dl = k;	
	assert_lit(asserted_lit);
	antecedent[l2v(asserted_lit)] = cnf.size() - 1;
	conflicting_clause_idx = -1;
}

void Solver::validate_assignment() {
	for (unsigned int i = 1; i <= nvars; ++i) if (state[i] == VarState::V_UNASSIGNED) {
		cout << "Unassigned var: " + to_string(i) << endl; // This is supposed to happen only if the variable does not appear in any clause
	}
	for (vector<Clause>::iterator it = cnf.begin(); it != cnf.end(); ++it) {
		int found = 0;
		for(clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c) 
			if (lit_state(*it_c) == LitState::L_SAT) found = 1;
		if (!found) {
			cout << "fail on clause: "; 
			it->print();
			cout << endl;
			for (clause_it it_c = it->cl().begin(); it_c != it->cl().end() && !found; ++it_c)
				cout << *it_c << " (" << (int) lit_state(*it_c) << ") ";
			cout << endl;
			Abort("Assignment validation failed", 3);
		}
	}
	for (vector<Lit>::iterator it = unaries.begin(); it != unaries.end(); ++it) {
		if (lit_state(*it) != LitState::L_SAT) 
			Abort("Assignment validation failed (unaries)", 3);
	}
	cout << "Assignment validated" << endl;
}

void Solver::restart() {	
	if (verbose_now()) cout << "restart" << endl;
	restart_threshold = static_cast<int>(restart_threshold * restart_multiplier);
	if (restart_threshold > restart_upper) {
		restart_threshold = restart_lower;
		restart_upper = static_cast<int>(restart_upper  * restart_multiplier);
		if (verbose >= 1) cout << "new restart upper bound = " << restart_upper << endl;
	}
	if (verbose >=1) cout << "restart: new threshold = " << restart_threshold << endl;
	++num_restarts;
	for (unsigned int i = 1; i <= nvars; ++i) 
		if (dlevel[i] > 0) {
			state[i] = VarState::V_UNASSIGNED;
			dlevel[i] = 0;
		}	
	trail.clear();
	qhead = 0;
	separators.clear(); 
	conflicts_at_dl.clear(); 
	if (VarDecHeuristic == VAR_DEC_HEURISTIC::MINISAT) {
		m_curr_activity = 0; // The activity does not really become 0. When it is reset in decide() it becomes the largets activity. 
		m_should_reset_iterators = true;
	}
	reset();
}

/// <summary>
/// Wrapper method for _solve()
/// calls _solve() and deals with _solve() result
/// </summary>
void Solver::solve() { 
	SolverState res = _solve(); 	
	Assert(res == SolverState::SAT || res == SolverState::UNSAT || res == SolverState::TIMEOUT);
	S.print_stats();
	switch (res) {
	case SolverState::SAT: {
		S.validate_assignment();
		string str = "solution in ",
			str1 = Assignment_file;
		cout << str + str1 << endl;
		cout << "SAT" << endl;
		break;
	}
	case SolverState::UNSAT: 
		cout << "UNSAT" << endl;
		break;
	case SolverState::TIMEOUT: 
		cout << "TIMEOUT" << endl;
		return;
	}	
	return;
}

/// <summary>
/// L2.1.SAT.pptx, slide 30
/// </summary>
/// <returns></returns>
SolverState Solver::_solve() {
	SolverState res;
	while (true) {
		if (timeout > 0 && cpuTime() - begin_time > timeout) return SolverState::TIMEOUT;
		while (true) {
			res = BCP();
			if (res == SolverState::UNSAT) return res; // conflict at decision level = 0
			if (res == SolverState::CONFLICT)
				backtrack(analyze(cnf[conflicting_clause_idx])); // cnf[conflicting_clause_idx] is a clause
			else break;
		}
		res = decide();
		if (res == SolverState::SAT) return res;
	}
}

#pragma endregion solving


/******************  main ******************************/
// file start -> p cnf (number of variables) (number of clauses)
int main(int argc, char** argv){
	begin_time = cpuTime();
	parse_options(argc, argv);
	
	ifstream in (argv[argc - 1]);
	if (!in.good()) Abort("cannot read input file", 1);	
	cout << "This is edusat" << endl;
	S.read_cnf(in);	// read cnf from input file	
	in.close();
	S.solve();	

	return 0;
}
