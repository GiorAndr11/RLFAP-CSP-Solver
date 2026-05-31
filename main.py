import os
import re
import sys
import time
import copy
import random
from collections import deque

# =====================================================================
# ΒΗΜΑ 1: PARSER ΔΕΔΟΜΕΝΩΝ & ΕΛΕΓΧΟΣ ΣΥΜΒΑΤΟΤΗΤΑΣ
# =====================================================================

def parse_rlfap_problem(problem_name, data_dir="data"):
    """
    Διαβάζει τα αρχεία domX.txt, varX.txt, ctrX.txt για ένα συγκεκριμένο πρόβλημα Χ.
    """
    dom_file = os.path.join(data_dir, f"dom{problem_name}.txt")
    var_file = os.path.join(data_dir, f"var{problem_name}.txt")
    ctr_file = os.path.join(data_dir, f"ctr{problem_name}.txt")
    
    if not (os.path.exists(dom_file) and os.path.exists(var_file) and os.path.exists(ctr_file)):
        return None
    
    # 1. Ανάγνωση Πεδίων Ορισμού (Domains)
    domains = {}
    with open(dom_file, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        for line in lines[1:]:
            line = line.strip()
            if not line:
                continue
            parts = list(map(int, line.split()))
            dom_id = parts[0]
            values = parts[2:]
            domains[dom_id] = values

    # 2. Ανάγνωση Μεταβλητών (Variables)
    variables = {}
    with open(var_file, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        for line in lines[1:]:
            line = line.strip()
            if not line:
                continue
            parts = list(map(int, line.split()))
            var_id = parts[0]
            dom_id = parts[1]
            variables[var_id] = dom_id

    # 3. Ανάγνωση Περιορισμών (Constraints)
    constraints = []
    with open(ctr_file, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        for line in lines[1:]:
            line = line.strip()
            if not line:
                continue
            match = re.match(r"(\d+)\s+(\d+)\s+([>=])\s+(\d+)", line)
            if match:
                var1 = int(match.group(1))
                var2 = int(match.group(2))
                operator = match.group(3)
                value = int(match.group(4))
                constraints.append((var1, var2, operator, value))
                
    return domains, variables, constraints


def is_consistent(var, val, assignment, constraints):
    """
    Ελέγχει αν η ανάθεση της τιμής 'val' στη μεταβλητή 'var' 
    είναι συμβατή με τις ήδη ανατεθείσες μεταβλητές.
    """
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
    """
    Επιλέγει την επόμενη μεταβλητή προς ανάθεση ανάλογα με τη στρατηγική.
    """
    unassigned = [v for v in variables if v not in assignment]
    
    # // Σημείο ελέγχου αν το πρόβλημα δεν έχει λύση
    if not unassigned:
        return None

    # // Σημείο επιλογής της επόμενης μεταβλητής
    if strategy == "random":
        return random.choice(unassigned)
        
    elif strategy == "mrv":
        min_size = min(len(current_domains[v]) for v in unassigned)
        candidates = [v for v in unassigned if len(current_domains[v]) == min_size]
        return random.choice(candidates)

# =====================================================================
# ΑΛΓΟΡΙΘΜΟΙ ΕΠΙΛΥΣΗΣ (ΕΡΩΤΗΜΑ 1)
# =====================================================================

def chronological_backtracking(assignment, variables, current_domains, constraints, strategy, metrics):
    if len(assignment) == len(variables):
        return assignment

    var = select_unassigned_variable(assignment, variables, current_domains, strategy)
    if var is None:
        return None

    values = list(current_domains[var])
    for val in values:
        metrics["assignments"] += 1
        
        if is_consistent(var, val, assignment, constraints):
            assignment[var] = val
            
            result = chronological_backtracking(assignment, variables, current_domains, constraints, strategy, metrics)
            if result is not None:
                return result
            
            del assignment[var]
            
    return None


def forward_checking_backtracking(assignment, variables, current_domains, constraints, strategy, metrics):
    if len(assignment) == len(variables):
        return assignment

    var = select_unassigned_variable(assignment, variables, current_domains, strategy)
    if var is None:
        return None

    values = list(current_domains[var])
    for val in values:
        metrics["assignments"] += 1
        
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
                            else:
                                # // Σημείο διαγραφής μία τιμής από το πεδίο ορισμού μεταβλητής
                                pass
                        
                        current_domains[other_var] = remaining_values
                        if not current_domains[other_var]:
                            failure = True
                            break
            
            if not failure:
                result = forward_checking_backtracking(assignment, variables, current_domains, constraints, strategy, metrics)
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
# ΚΕΝΤΡΙΚΟΣ ΜΗΧΑΝΙΣΜΟΣ ΕΚΤΕΛΕΣΗΣ ΠΕΙΡΑΜΑΤΩΝ
# =====================================================================

def run_experiments_for_problem(prob_name, data_dir="data"):
    parsed = parse_rlfap_problem(prob_name, data_dir)
    if not parsed:
        print(f"Το πρόβλημα {prob_name} δεν βρέθηκε στο φάκελο '{data_dir}'.")
        return None
        
    domains, variables, constraints = parsed
    results = {}

    # --- ΕΡΩΤΗΜΑ 1 ---
    # 1. BT + Random
    cd = {v: list(domains[variables[v]]) for v in variables}
    m = {"assignments": 0}; start = time.perf_counter()
    sol = chronological_backtracking({}, variables, cd, constraints, "random", m)
    t = time.perf_counter() - start
    results["BT_Random"] = {"solved": sol is not None, "assigns": m["assignments"], "time": t}

    # 2. BT + MRV
    cd = {v: list(domains[variables[v]]) for v in variables}
    m = {"assignments": 0}; start = time.perf_counter()
    sol = chronological_backtracking({}, variables, cd, constraints, "mrv", m)
    t = time.perf_counter() - start
    results["BT_MRV"] = {"solved": sol is not None, "assigns": m["assignments"], "time": t}

    # 3. FC + Random
    cd = {v: list(domains[variables[v]]) for v in variables}
    m = {"assignments": 0}; start = time.perf_counter()
    sol = forward_checking_backtracking({}, variables, cd, constraints, "random", m)
    t = time.perf_counter() - start
    results["FC_Random"] = {"solved": sol is not None, "assigns": m["assignments"], "time": t}

    # 4. FC + MRV
    cd = {v: list(domains[variables[v]]) for v in variables}
    m = {"assignments": 0}; start = time.perf_counter()
    sol = forward_checking_backtracking({}, variables, cd, constraints, "mrv", m)
    t = time.perf_counter() - start
    results["FC_MRV"] = {"solved": sol is not None, "assigns": m["assignments"], "time": t}

    # --- ΕΡΩΤΗΜΑ 2 (Με AC-3 Προ-επεξεργασία) ---
    for algo_name, solver_func in [("AC3_BT_Random", "chronological"), ("AC3_BT_MRV", "chronological"), 
                                   ("AC3_FC_Random", "forward_checking"), ("AC3_FC_MRV", "forward_checking")]:
        strategy = "mrv" if "MRV" in algo_name else "random"
        cd = {v: list(domains[variables[v]]) for v in variables}
        
        start = time.perf_counter()
        is_consistent_prob, deleted_vals = ac3(variables, cd, constraints)
        
        sol = None
        m = {"assignments": 0}
        if is_consistent_prob:
            if solver_func == "chronological":
                sol = chronological_backtracking({}, variables, cd, constraints, strategy, m)
            else:
                sol = forward_checking_backtracking({}, variables, cd, constraints, strategy, m)
                
        t = time.perf_counter() - start
        results[algo_name] = {"deleted": deleted_vals, "solved": sol is not None, "assigns": m["assignments"], "time": t}

    return results

if __name__ == "__main__":
    # Λίστα με τα ονόματα των 12 προβλημάτων (π.χ. αν είναι αριθμημένα 1 έως 12 ή έχουν συγκεκριμένα ονόματα)
    # Μπορείς να τροποποιήσεις τη λίστα ανάλογα με τα ακριβή ονόματα των αρχείων σου στο rlfaps.rar
    problems = [str(i) for i in range(1, 13)] 
    
    print("Έναρξη πειραμάτων για τα προβλήματα RLFAPs...")
    print("-" * 80)
    
    for prob in problems:
        print(f"\n>>> Επεξεργασία Προβλήματος: {prob} <<<")
        res = run_experiments_for_problem(prob)
        if not res:
            continue
            
        print("\n[ΕΡΩΤΗΜΑ 1] Αποτελέσματα:")
        print(f"{'Αλγόριθμος':<15} | {'Λύση':<8} | {'Αναθέσεις':<12} | {'Χρόνος (sec)':<12}")
        print("-" * 55)
        for k in ["BT_Random", "BT_MRV", "FC_Random", "FC_MRV"]:
            sol_str = "Βρέθηκε" if res[k]["solved"] else "Όχι"
            print(f"{k:<15} | {sol_str:<8} | {res[k]['assigns']:<12} | {res[k]['time']:.4f}")
            
        print("\n[ΕΡΩΤΗΜΑ 2] Αποτελέσματα (με AC-3):")
        print(f"{'Αλγόριθμος':<18} | {'Διαγραφές':<9} | {'Λύση':<8} | {'Αναθέσεις':<12} | {'Χρόνος (sec)':<12}")
        print("-" * 70)
        for k in ["AC3_BT_Random", "AC3_BT_MRV", "AC3_FC_Random", "AC3_FC_MRV"]:
            sol_str = "Βρέθηκε" if res[k]["solved"] else "Όχι"
            print(f"{k:<18} | {res[k]['deleted']:<9} | {sol_str:<8} | {res[k]['assigns']:<12} | {res[k]['time']:.4f}")
        print("=" * 80)
