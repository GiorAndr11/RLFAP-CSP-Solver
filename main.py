import os
import sys
import time
import copy
import random
from collections import deque

# =====================================================================
# ΒΗΜΑ 1: ΑΠΛΟΠΟΙΗΜΕΝΟΣ ΚΑΙ ΘΩΡΑΚΙΣΜΕΝΟΣ PARSER
# =====================================================================

def parse_rlfap_problem(problem_name, data_dir="data"):
    dom_file = os.path.join(data_dir, f"dom{problem_name}.txt")
    var_file = os.path.join(data_dir, f"var{problem_name}.txt")
    ctr_file = os.path.join(data_dir, f"ctr{problem_name}.txt")
    
    if not (os.path.exists(dom_file) and os.path.exists(var_file) and os.path.exists(ctr_file)):
        return None
    
    # 1. Ανάγνωση Πεδίων Ορισμού
    domains = {}
    with open(dom_file, 'r', encoding='utf-8') as f:
        lines = [line.strip() for line in f if line.strip()]
        for line in lines[1:]:
            parts = list(map(int, line.split()))
            if len(parts) >= 3:
                dom_id = parts[0]
                values = parts[2:]
                domains[dom_id] = values

    # 2. Ανάγνωση Μεταβλητών
    variables = {}
    with open(var_file, 'r', encoding='utf-8') as f:
        lines = [line.strip() for line in f if line.strip()]
        for line in lines[1:]:
            parts = list(map(int, line.split()))
            if len(parts) == 2:
                var_id = parts[0]
                dom_id = parts[1]
                variables[var_id] = dom_id

    # 3. Ανάγνωση Περιορισμών
    constraints = []
    with open(ctr_file, 'r', encoding='utf-8') as f:
        lines = [line.strip() for line in f if line.strip()]
        for line in lines[1:]:
            clean_line = line.replace('>', ' > ').replace('=', ' = ')
            parts = clean_line.split()
            if len(parts) == 4:
                try:
                    var1 = int(parts[0])
                    var2 = int(parts[1])
                    operator = parts[2]
                    value = int(parts[3])
                    constraints.append((var1, var2, operator, value))
                except ValueError:
                    continue
                
    print(f"   [Parser OK]: Φορτώθηκαν {len(variables)} μεταβλητές, {len(domains)} πεδία και {len(constraints)} περιορισμοί.")
    return domains, variables, constraints


def is_consistent(var, val, assignment, constraints):
    # // Σημείο ελέγχου εγκυρότητας μιας ανάθεσης τιμής
    for var1, var2, operator, alpha in constraints:
        if var1 == var or var2 == var:
            other_var = var2 if var1 == var else var1
            if other_var in assignment:
                val1 = val if var1 == var else assignment[other_var]
                val2 = assignment[other_var] if var1 == var else val
                if operator == '>':
                    if not (abs(val1 - val2) > alpha):
                        return False
                elif operator == '=':
                    if not (val1 - val2 == alpha):
                        return False
    return True

# =====================================================================
# ΒΗΜΑ 2: ΜΗΧΑΝΙΣΜΟΙ ΕΠΙΛΟΓΗΣ ΜΕΤΑΒΛΗΤΩΝ
# =====================================================================

def select_unassigned_variable(assignment, variables, current_domains, strategy):
    unassigned = [v for v in variables if v not in assignment]
    if not unassigned:
        return None
    # // Σημείο επιλογής της επόμενης μεταβλητής
    if strategy == "random":
        return unassigned[0]
    elif strategy == "mrv":
        min_size = min(len(current_domains[v]) for v in unassigned)
        candidates = [v for v in unassigned if len(current_domains[v]) == min_size]
        return candidates[0]

# =====================================================================
# ΑΛΓΟΡΙΘΜΟΙ ΕΠΙΛΥΣΗΣ ΜΕ ΔΙΠΛΟ ΚΟΦΤΗ (ΧΡΟΝΟΣ & ΑΝΑΘΕΣΕΙΣ)
# =====================================================================

def fast_backtracking_double_limit(variables, current_domains, constraints, strategy, metrics, start_time, max_assigns, timeout_sec=30.0):
    stack = [({}, [])]
    
    while stack:
        assignment, selected_vars = stack.pop()
        
        if len(assignment) == len(variables):
            return assignment
            
        # Κόφτης 1: Έλεγχος Αναθέσεων
        if metrics["assignments"] > max_assigns:
            metrics["timeout"] = True
            return None

        # Κόφτης 2: Έλεγχος Πραγματικού Χρόνου
        if time.perf_counter() - start_time > timeout_sec:
            metrics["timeout"] = True
            return None
            
        var = select_unassigned_variable(assignment, variables, current_domains, strategy)
        if var is None:
            continue
            
        for val in current_domains[var]:
            metrics["assignments"] += 1
            if is_consistent(var, val, assignment, constraints):
                new_assignment = assignment.copy()
                new_assignment[var] = val
                stack.append((new_assignment, selected_vars + [var]))
                
    return None


def forward_checking_backtracking_double_limit(assignment, variables, current_domains, constraints, strategy, metrics, start_time, max_assigns, timeout_sec=30.0):
    if len(assignment) == len(variables):
        return assignment

    # Κόφτης 1: Έλεγχος Αναθέσεων
    if metrics["assignments"] > max_assigns:
        metrics["timeout"] = True
        return None

    # Κόφτης 2: Έλεγχος Πραγματικού Χρόνου
    if time.perf_counter() - start_time > timeout_sec:
        metrics["timeout"] = True
        return None

    var = select_unassigned_variable(assignment, variables, current_domains, strategy)
    if var is None:
        return None

    for val in list(current_domains[var]):
        metrics["assignments"] += 1
        
        # Περιοδικός έλεγχος χρόνου και αναθέσεων ανά 500 βήματα
        if metrics["assignments"] % 500 == 0:
            if metrics["assignments"] > max_assigns or (time.perf_counter() - start_time > timeout_sec):
                metrics["timeout"] = True
                return None

        if is_consistent(var, val, assignment, constraints):
            assignment[var] = val
            domains_backup = copy.deepcopy(current_domains)
            current_domains[var] = [val]
            
            failure = False
            for var1, var2, operator, alpha in constraints:
                if var1 == var or var2 == var:
                    other_var = var2 if var1 == var else var1
                    if other_var not in assignment:
                        # // Σημείο ελέγχου αν υποστηρίζεται μία τιμή μεταβλητής από τιμές άλλης μεταβλητής
                        remaining_values = []
                        for other_val in current_domains[other_var]:
                            val1 = val if var1 == var else other_val
                            val2 = other_val if var1 == var else val
                            
                            satisfied = False
                            if operator == '>':
                                if abs(val1 - val2) > alpha:
                                    satisfied = True
                            elif operator == '=':
                                if val1 - val2 == alpha:
                                    satisfied = True
                                    
                            if satisfied:
                                remaining_values.append(other_val)
                        
                        current_domains[other_var] = remaining_values
                        if not current_domains[other_var]:
                            failure = True
                            break
            
            if not failure:
                result = forward_checking_backtracking_double_limit(assignment, variables, current_domains, constraints, strategy, metrics, start_time, max_assigns, timeout_sec)
                if result is not None:
                    return result
            
            del assignment[var]
            current_domains = domains_backup
            
    return None

# =====================================================================
# ΑΛΓΟΡΙΘΜΟΣ AC-3 (ΕΡΩΤΗΜΑ 2)
# =====================================================================

def ac3(variables, current_domains, constraints):
    queue = deque()
    for var1, var2, operator, alpha in constraints:
        queue.append((var1, var2, operator, alpha, True))
        queue.append((var2, var1, operator, alpha, False))

    total_deleted_values = 0
    while queue:
        var_i, var_j, operator, alpha, is_direct = queue.popleft()
        revised, deleted_count = revise(var_i, var_j, operator, alpha, is_direct, current_domains)
        
        if revised:
            total_deleted_values += deleted_count
            # // Σημείο ελέγχου αν το πρόβλημα δεν έχει λύση
            if len(current_domains[var_i]) == 0:
                return False, total_deleted_values
                
            for v1, v2, op, a in constraints:
                if v1 == var_i and v2 != var_j:
                    queue.append((v2, var_i, op, a, False))
                elif v2 == var_i and v1 != var_j:
                    queue.append((v1, var_i, op, a, True))
                    
    return True, total_deleted_values


def revise(var_i, var_j, operator, alpha, is_direct, current_domains):
    revised = False
    deleted_count = 0
    kept_values = []
    
    for val_i in current_domains[var_i]:
        # // Σημείο ελέγχου αν υποστηρίζεται μία τιμή μεταβλητής από τιμές άλλης μεταβλητής
        has_support = False
        for val_j in current_domains[var_j]:
            val1 = val_i if is_direct else val_j
            val2 = val_j if is_direct else val_i
            if operator == '>':
                if abs(val1 - val2) > alpha:
                    has_support = True
                    break
            elif operator == '=':
                if val1 - val2 == alpha:
                    has_support = True
                    break
                    
        if has_support:
            kept_values.append(val_i)
        else:
            # // Σημείο διαγραφής μία τιμής από το πεδίο ορισμού μεταβλητής
            revised = True
            deleted_count += 1
            
    if revised:
        current_domains[var_i] = kept_values
        
    return revised, deleted_count

# =====================================================================
# ΑΥΤΟΜΑΤΗ ΑΝΑΖΗΤΗΣΗ ΠΡΟΒΛΗΜΑΤΩΝ ΣΤΟΝ ΦΑΚΕΛΟ
# =====================================================================

def discover_problems(data_dir="data"):
    if not os.path.exists(data_dir):
        return []
    problems = []
    for filename in os.listdir(data_dir):
        if filename.startswith("dom") and filename.endswith(".txt"):
            prob_name = filename[3:-4]
            if (os.path.exists(os.path.join(data_dir, f"var{prob_name}.txt")) and 
                os.path.exists(os.path.join(data_dir, f"ctr{prob_name}.txt"))):
                problems.append(prob_name)
    try:
        problems.sort(key=int)
    except ValueError:
        problems.sort()
    return problems

# =====================================================================
# ΚΕΝΤΡΙΚΟΣ ΜΗΧΑΝΙΣΜΟΣ ΕΚΤΕΛΕΣΗΣ ΠΕΙΡΑΜΑΤΩΝ
# =====================================================================

def run_experiments_for_problem(prob_name, data_dir="data"):
    print(f"-> Ξεκινάει το διάβασμα του προβλήματος {prob_name}...")
    parsed = parse_rlfap_problem(prob_name, data_dir)
    if not parsed:
        return None
        
    domains, variables, constraints = parsed
    results = {}

    # ΡΥΘΜΙΣΗ ΟΡΙΩΝ (30 SEC TIMEOUT & SWEET SPOT ΑΝΑΘΕΣΕΩΝ)
    TIMEOUT_SEC = 30.0
    BT_LIMIT = 50000
    FC_LIMIT = 5000000

    print("   [Running]: BT_Random...")
    cd = {v: list(domains[variables[v]]) for v in variables}
    m = {"assignments": 0, "timeout": False}; start = time.perf_counter()
    sol = fast_backtracking_double_limit(variables, cd, constraints, "random", m, start, BT_LIMIT, TIMEOUT_SEC)
    results["BT_Random"] = {"solved": sol is not None, "assigns": m["assignments"], "time": time.perf_counter() - start, "timeout": m["timeout"]}

    print("   [Running]: BT_MRV...")
    cd = {v: list(domains[variables[v]]) for v in variables}
    m = {"assignments": 0, "timeout": False}; start = time.perf_counter()
    sol = fast_backtracking_double_limit(variables, cd, constraints, "mrv", m, start, BT_LIMIT, TIMEOUT_SEC)
    results["BT_MRV"] = {"solved": sol is not None, "assigns": m["assignments"], "time": time.perf_counter() - start, "timeout": m["timeout"]}

    print("   [Running]: FC_Random...")
    cd = {v: list(domains[variables[v]]) for v in variables}
    m = {"assignments": 0, "timeout": False}; start = time.perf_counter()
    sol = forward_checking_backtracking_double_limit({}, variables, cd, constraints, "random", m, start, FC_LIMIT, TIMEOUT_SEC)
    results["FC_Random"] = {"solved": sol is not None, "assigns": m["assignments"], "time": time.perf_counter() - start, "timeout": m["timeout"]}

    print("   [Running]: FC_MRV...")
    cd = {v: list(domains[variables[v]]) for v in variables}
    m = {"assignments": 0, "timeout": False}; start = time.perf_counter()
    sol = forward_checking_backtracking_double_limit({}, variables, cd, constraints, "mrv", m, start, FC_LIMIT, TIMEOUT_SEC)
    results["FC_MRV"] = {"solved": sol is not None, "assigns": m["assignments"], "time": time.perf_counter() - start, "timeout": m["timeout"]}

    # --- ΕΡΩΤΗΜΑ 2 (Με AC-3) ---
    print("   [Running]: AC-3 Preprocessing + Solvers...")
    for algo_name, solver_func in [("AC3_BT_Random", "chronological"), ("AC3_BT_MRV", "chronological"), 
                                   ("AC3_FC_Random", "forward_checking"), ("AC3_FC_MRV", "forward_checking")]:
        strategy = "mrv" if "MRV" in algo_name else "random"
        cd = {v: list(domains[variables[v]]) for v in variables}
        
        start = time.perf_counter()
        is_consistent_prob, deleted_vals = ac3(variables, cd, constraints)
        
        sol = None
        m = {"assignments": 0, "timeout": False}
        
        if is_consistent_prob:
            if solver_func == "chronological":
                sol = fast_backtracking_double_limit(variables, cd, constraints, strategy, m, start, BT_LIMIT, TIMEOUT_SEC)
            else:
                sol = forward_checking_backtracking_double_limit({}, variables, cd, constraints, strategy, m, start, FC_LIMIT, TIMEOUT_SEC)
                
        results[algo_name] = {"deleted": deleted_vals, "solved": sol is not None, "assigns": m["assignments"], "time": time.perf_counter() - start, "timeout": m["timeout"]}

    return results

# =====================================================================
# ΚΥΡΙΑ ΕΚΤΕΛΕΣΗ
# =====================================================================

if __name__ == "__main__":
    problems = discover_problems("data")
    
    if not problems:
        print("Σφάλμα: Δεν βρέθηκαν έγκυρα αρχεία προβλημάτων στον φάκελο 'data/'.")
        sys.exit(1)
        
    print(f"Βρέθηκαν {len(problems)} προβλήματα προς επίλυση: {', '.join(problems)}")
    print("-" * 80)
    
    for prob in problems:
        print(f"\n>>> ΕΠΕΞΕΡΓΑΣΙΑ ΠΡΟΒΛΗΜΑΤΟΣ: {prob} <<<")
        res = run_experiments_for_problem(prob)
        if not res:
            continue
            
        print("\n   [ΕΡΩΤΗΜΑ 1] Αποτελέσματα:")
        print(f"   {'Αλγόριθμος':<15} | {'Λύση':<8} | {'Αναθέσεις':<12} | {'Χρόνος (sec)':<12}")
        print("   " + "-" * 55)
        for k in ["BT_Random", "BT_MRV", "FC_Random", "FC_MRV"]:
            sol_str = "Timeout" if res[k]["timeout"] else ("Βρέθηκε" if res[k]["solved"] else "Όχι")
            print(f"   {k:<15} | {sol_str:<8} | {res[k]['assigns']:<12} | {res[k]['time']:.4f}")
            
        print("\n   [ΕΡΩΤΗΜΑ 2] Αποτελέσματα (με AC-3):")
        print(f"   {'Αλγόριθμος':<18} | {'Διαγραφές':<9} | {'Λύση':<8} | {'Αναθέσεις':<12} | {'Χρόνος (sec)':<12}")
        print("   " + "-" * 70)
        for k in ["AC3_BT_Random", "AC3_BT_MRV", "AC3_FC_Random", "AC3_FC_MRV"]:
            sol_str = "Timeout" if res[k]["timeout"] else ("Βρέθηκε" if res[k]["solved"] else "Όχι")
            print(f"   {k:<18} | {res[k]['deleted']:<9} | {sol_str:<8} | {res[k]['assigns']:<12} | {res[k]['time']:.4f}")
        print("=" * 80)
