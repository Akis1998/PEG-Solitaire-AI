import os
import time
from dataclasses import dataclass
import sys
import heapq
import copy
import random

WALL = 0
PEG = 1
HOLE = 2

# οι επιτρεπτές κινήσεις (κατευθύνσεις) των αλμάτων
moves = ((0, 1), (1, 0), (0, -1), (-1, 0))


def get_board_from_file(filename):
    # Δέχεται το όνομα του αρχείου που περιέχει το πρόβλημα
    # και επιστρέφει το ταμπλό (διδιάστατη λίστα ακεραίων)

    with open(filename) as f:
        number_of_lines, number_of_elements = [int(x) for x in next(f).split()]
        array = []
        for i, line in enumerate(f):
            if i == number_of_lines:
                break
            line_list = [int(x) for x in line.split()]
            assert (number_of_elements == len(line_list))
            array.append([int(x) for x in line.split()])
    return array


def get_solution_from_file(filename):
    # Ανάγνωση λύσης από αρχείο και μετατροπή στη δική μας
    # μορφή λύσης για έλεγχο αργότερα
    with open(filename) as f:
        solution = []
        pegs = [int(x) for x in next(f).split()][0]
        for line in f:
            solution.append([int(x) for x in line.split()])

    return pegs, [(x[0] - 1, x[1] - 1, (x[2] - x[0]) // 2, (x[3] - x[1]) // 2) for x in solution]


def sum_pegs(board):
    # Υπολογίζει τον αριθμό των πασσάλων στον πίνακα
    return sum([row.count(PEG) for row in board])


def flip_hhp(board, y, x, y0, x0):
    # Aλλάζει τις 3 διαδοχικές θέσεις του πίνακα
    # που αρχίζουν από τη θέση (y, x) με κατεύθυνση (y0, x0)
    # σε κενό, κενό, πάσσαλος.
    board[y][x] = HOLE
    board[y + y0][x + x0] = HOLE
    board[y + 2 * y0][x + 2 * x0] = PEG


def flip_pph(board, y, x, y0, x0):
    # Aλλάζει τις 3 διαδοχικές θέσεις του πίνακα
    # που αρχίζουν από τη θέση (y, x) με κατεύθυνση (y0, x0)
    # σε πάσσαλος, πάσσαλος, κενό.
    board[y][x] = PEG
    board[y + y0][x + x0] = PEG
    board[y + 2 * y0][x + 2 * x0] = HOLE


def pretty_print(board):
    # Μία στοιχειωδώς αισθητική εμφάνιση του προβλήματος προς επίλυση
    output = ['  ', 'I ', 'O ']

    for y, row in enumerate(board):
        for x, col in enumerate(row):
            print(output[board[y][x]], end='')
        print()
    print()


def symmetries(board_in):
    # Εξετάζουμε το αναλλοίωτο του πίνακα ως προς τις 8 δυνατές συμμετρίες
    h, w = len(board_in), len(board_in[0])
    board = [[0 if _ == WALL else 1 for _ in a] for a in board_in]

    # συμμετρίες που είναι δυνατόν να υπάρξουν μόνο σε τετραγωνικά προβλήματα
    just_square_symmetries = [
        lambda x: list(map(list, zip(*[_[::-1] for _ in x[::-1]]))),
        # συμμετρία ως προς την αντιδιαγώνιο
        lambda x: list(map(list, zip(*x))),
        # συμμετρία ως προς τη διαγώνιο
        lambda x: list(map(list, zip(*x[::-1]))),
        # στροφή ωρολογιακά κατά 90
        lambda x: list(map(list, zip(*[_[::-1] for _ in x])))]
    # στροφή αντιωρολογιακά κατά 90

    # δυνατές συμμετρίες για ορθογώνια προβλήματα
    orthogonal_symmetries = [
        lambda x: x,
        # ταυτότητα
        lambda x: [_[::-1] for _ in x],
        # κατακόρυφη συμμετρία
        lambda x: [_[::-1] for _ in x][::-1],
        # στροφή κατά 180
        lambda x: x[::-1]]
    # οριζόντια συμμετρία

    # προφανώς η ταυτότητα θα ανήκει στη λίστα αλλά την εξετάζουμε ούτως ή άλλως
    return [symmetry for symmetry in
            (orthogonal_symmetries + (just_square_symmetries if h == w else []))
            if symmetry(board) == board]


def construct_solution_from_instance(instance):
    # Αναρρίχηση μέχρι την ρίζα του δέντρου και αποθήκευση των κινήσεων
    # Χρησιμοποιείται από τις BeFS συναρτήσεις
    moves_list = []
    while instance.parent:
        moves_list.insert(0, instance.move)
        instance = instance.parent
    return moves_list


def compute_center(board):
    # Υπολογισμός του κέντρου με βάση τους υπάρχοντες πασσάλους
    # Χρησιμοποιείται μόνο από τις BeFS συναρτήσεις

    sumy, sumx, sumall = 0, 0, 0
    for y in range(len(board)):
        for x in range(len(board[0])):
            if board[y][x] == PEG:
                sumy += y
                sumx += x
                sumall += 1
    return int(sumy / sumall), int(sumx / sumall)


def befs_generic(original_board, cost_function):
    @dataclass
    class Instance:
        def __init__(self, pegs, board, move, parent):
            self.pegs = pegs  # αριθμός πασσάλων
            self.board = board  # η αντιγραφή γίνεται πριν τη δημιουργία του αντικειμένου
            self.move = move  # κίνηση από την οποία προήλθε το στιγμιότυπο
            self.parent = parent  # "δείκτης" στο πρόβλημα-γονέα
            self.heuristic = 0  # τιμή της ευρετικής (θα μπορούσε και None αρχικά)

    def compute_first_heuristic(instance):
        instance.heuristic = 0
        for y in range(height):
            for x in range(width):
                if instance.board[y][x] == PEG:
                    instance.heuristic += cost_function(y, x)

    def compute_not_first_heuristic(instance):
        instance.heuristic = instance.parent.heuristic
        ym, xm, y0, x0 = instance.move
        instance.heuristic -= cost_function(ym, xm)
        instance.heuristic -= cost_function(ym + y0, xm + x0)
        instance.heuristic += cost_function(ym + 2 * y0, xm + 2 * x0)

    def befs_rec(instance):
        pegs = instance.pegs
        board = instance.board

        if pegs == 1:
            return construct_solution_from_instance(instance)

        for y, row in enumerate(board):  # για κάθε πάσσαλο
            for x, col in enumerate(row):
                if board[y][x] != PEG:
                    continue
                for y0, x0 in moves:  # για κάθε δυνατή κίνηση
                    if 0 <= y + 2 * y0 < height and 0 <= x + 2 * x0 < width and \
                            board[y + y0][x + x0] == PEG and \
                            board[y + 2 * y0][x + 2 * x0] == HOLE:
                        flip_hhp(board, y, x, y0, x0)  # κάνε την κίνηση αφού είναι εφικτή
                        # και εξέτασε παρακάτω αν το πρόβλημα ή κάποιο συμμετρικό του έχει συναντηθεί

                        # Αν δεν το συναντήσαμε, το προσθέτουμε και δημιουργούμε το νέο στιγμιότυπο
                        if not any([tuple(tuple(_) for _ in symmetry(board)) in boards_seen
                                    for symmetry in problem_symmetries]):
                            boards_seen.add(tuple(tuple(_) for _ in board))
                            new_move = (y, x, y0, x0)
                            new_board = copy.deepcopy(board)
                            # Για το νέο στιγμιότυπο υπολόγισε την ευρετική τιμή και με βάση αυτή
                            # ένθεσέ το στην ουρά προτεραιότητας
                            current_instance = Instance(pegs - 1, new_board, new_move, instance)
                            compute_not_first_heuristic(current_instance)
                            heapq.heappush(unexplored_instances,
                                           (current_instance.heuristic, current_instance))
                        # σε κάθε περίπτωση undo το flip για τον board
                        flip_pph(board, y, x, y0, x0)

    boards_seen = set()  # σύνολο περιγραφών (ή των συμμετρικών) που έχουμε δει
    unexplored_instances = []  # τρέχουσα λίστα προς εξερεύνηση (θα γίνει ουρά προτεραιότητας)
    height = len(original_board)
    width = len(original_board[0])
    problem_symmetries = symmetries(original_board)  # δυνατές συμμετρίες για το πρόβλημα

    ''' Αφού δημιουργήσουμε το πρώτο στιγμιότυπο με την περιγραφή του αρχικού προβλήματος,
        βρούμε την τιμή της ευρετικής συνάρτησης, προσθέτουμε το πρόβλημα στο σύνολο με τα
        προβλήματα που έχουμε δει και το στιγμιότυπο στην ουρά προτεραιότητας '''
    root_instance = Instance(sum_pegs(original_board), original_board, None, None)
    compute_first_heuristic(root_instance)
    boards_seen.add(tuple(tuple(_) for _ in original_board))
    heapq.heappush(unexplored_instances, (root_instance.heuristic, root_instance))

    ''' Όσο δεν έχει βρεθεί λύση και υπάρχουν στιγμιότυπα προς επίλυση, διαλέγουμε αυτό με 
        τη χαμηλότερη ευρετική τιμή και το επισκεφτόμαστε  '''
    while unexplored_instances:
        best_instance = heapq.heappop(unexplored_instances)[1]
        solution = befs_rec(best_instance)
        if solution:
            return solution
    return None


def befs_manhattan(original_board):
    @dataclass
    class Instance:
        def __init__(self, pegs, board, move, parent):
            self.pegs = pegs
            self.board = board  # η αντιγραφή γίνεται πριν τη δημιουργία του αντικειμένου
            self.move = move
            self.parent = parent
            self.heuristic = 0

    def compute_manhattan(instance):
        instance.heuristic = 0
        if instance.parent:
            instance.heuristic = instance.parent.heuristic

            ym, xm, y0, x0 = instance.move
            for y in range(height):
                for x in range(width):
                    if instance.board[y][x] == PEG and \
                            (y, x) not in [(ym, xm), (ym + y0, xm + x0), (ym + 2 * y0, xm + 2 * x0)]:
                        instance.heuristic -= abs(y - ym) + abs(x - xm)
                        instance.heuristic -= abs(y - (ym + y0)) + abs(x - (xm + x0))
                        instance.heuristic += abs(y - (ym + 2 * y0)) + abs(x - (xm + 2 * x0))

            instance.heuristic -= 1
        else:
            for y in range(height):
                for x in range(width):
                    if instance.board[y][x] == PEG:
                        for yy in range(y):
                            for xx in range(width):
                                if instance.board[yy][xx] == PEG:
                                    instance.heuristic += abs(xx - x) + abs(y - yy)
                        for xx in range(x):
                            if instance.board[y][xx] == PEG:
                                instance.heuristic += abs(xx - x)

        return instance.heuristic

    def befs_rec(instance):
        pegs = instance.pegs
        board = instance.board
        # move = instance.move
        # parent = instance.parent
        if pegs == 1:
            return construct_solution_from_instance(instance)

        for y, row in enumerate(board):
            for x, col in enumerate(row):
                if board[y][x] != PEG:
                    continue
                for y0, x0 in moves:
                    if 0 <= y + 2 * y0 < height and 0 <= x + 2 * x0 < width and \
                            board[y + y0][x + x0] == PEG and \
                            board[y + 2 * y0][x + 2 * x0] == HOLE:
                        flip_hhp(board, y, x, y0, x0)

                        if not any([tuple(tuple(_) for _ in symmetry(board)) in boards_seen
                                    for symmetry in problem_symmetries]):
                            boards_seen.add(tuple(tuple(_) for _ in board))
                            new_move = (y, x, y0, x0)
                            new_board = copy.deepcopy(board)
                            current_instance = Instance(pegs - 1, new_board, new_move, instance)
                            heuristic_value = compute_manhattan(current_instance)
                            heapq.heappush(unexplored_instances,
                                           (heuristic_value, current_instance))
                        flip_pph(board, y, x, y0, x0)
                        # σε κάθε περίπτωση undo το flip για τον board

    boards_seen = set()
    problem_symmetries = symmetries(original_board)

    unexplored_instances = []
    height = len(original_board)
    width = len(original_board[0])
    boards_seen.add(tuple(tuple(_) for _ in original_board))

    root_instance = Instance(sum_pegs(original_board), original_board, None, None)
    max_manhattan = compute_manhattan(root_instance)
    heapq.heappush(unexplored_instances, (max_manhattan, root_instance))
    while unexplored_instances:
        best_instance = heapq.heappop(unexplored_instances)[1]
        solution = befs_rec(best_instance)
        if solution:
            return solution
    return None


def befs_euclidean(board):
    center_y, center_x = compute_center(board)

    return befs_generic(board,
                        lambda y, x: (y - center_y)**2 + (x - center_x)**2)


def befs_exponential(board):
    center_y, center_x = compute_center(board)

    return befs_generic(board,
                        lambda y, x: 2**abs(y - center_y) + 2**abs(x - center_x))


def befs_max_exponential(board):
    center_y, center_x = compute_center(board)

    return befs_generic(board,
                        lambda y, x: 2**max(abs(y - center_y), abs(x - center_x)))


def dfs_recursive(original_board):
    def dfs_recursive_inner(board, pegs):
        if pegs == 1:
            return path

        for y, row in enumerate(board):
            for x, col in enumerate(row):
                # print(x, y)
                if board[y][x] == PEG:
                    for y0, x0 in moves:
                        if not (0 <= y + 2 * y0 < height and 0 <= x + 2 * x0 < width):
                            continue
                        if board[y + y0][x + x0] == PEG and board[y + 2 * y0][x + 2 * x0] == HOLE:
                            flip_hhp(board, y, x, y0, x0)
                            seen_before = False
                            for symmetry in problem_symmetries:
                                if tuple(tuple(_) for _ in symmetry(board)) in boards_seen:
                                    seen_before = True
                                    break
                            if not seen_before:
                                boards_seen.add(tuple(tuple(_) for _ in board))
                                path.append((y, x, y0, x0))
                                if dfs_recursive_inner(board, pegs - 1):
                                    return path
                                path.pop()
                                # flip_pph(board, y, x, y0, x0)
                            flip_pph(board, y, x, y0, x0)
        return []

    boards_seen = set()
    problem_symmetries = symmetries(original_board)

    height = len(original_board)
    width = len(original_board[0])
    path = []
    temp_board = copy.deepcopy(original_board)
    boards_seen.add(tuple(tuple(_) for _ in temp_board))
    return dfs_recursive_inner(temp_board, sum_pegs(temp_board))


def dfs_recursive_random(original_board):
    def dfs_recursive_inner(board, pegs):
        if pegs == 1:
            # print("Solved!")
            # print(moves_taken)
            return path

        for y, row in enumerate(board):
            for x, col in enumerate(row):
                # print(x, y)
                if board[y][x] == PEG:
                    for y0, x0 in random.sample(list(moves), len(moves)):
                        if not (0 <= y + 2 * y0 < height and 0 <= x + 2 * x0 < width):
                            continue
                        if board[y + y0][x + x0] == PEG and board[y + 2 * y0][x + 2 * x0] == HOLE:
                            board[y][x] = HOLE
                            board[y + y0][x + x0] = HOLE
                            board[y + 2 * y0][x + 2 * x0] = PEG
                            seen_before = False
                            for symmetry in problem_symmetries:
                                if tuple(tuple(_) for _ in symmetry(board)) in boards_seen:
                                    seen_before = True
                                    break
                            if not seen_before:
                                boards_seen.add(tuple(tuple(_) for _ in board))
                                path.append((y, x, y0, x0))
                                if dfs_recursive_inner(board, pegs - 1):
                                    return path
                                path.pop()
                                # flip_pph(board, y, x, y0, x0)
                            board[y][x] = PEG
                            board[y + y0][x + x0] = PEG
                            board[y + 2 * y0][x + 2 * x0] = HOLE
        return []

    boards_seen = set()
    problem_symmetries = symmetries(original_board)

    height = len(original_board)
    width = len(original_board[0])
    path = []
    temp_board = copy.deepcopy(original_board)
    boards_seen.add(tuple(tuple(_) for _ in temp_board))
    return dfs_recursive_inner(temp_board, sum_pegs(temp_board))


def validate_solution(solution, board):
    if not solution:
        print('Δεν υπάρχει λύση')
        return False
    test_board = copy.deepcopy(board)
    print("Έλεγχος λύσης...", end=' ')
    move_index = 0
    for y, x, y0, x0 in solution:
        move_index += 1
        try:
            assert test_board[y][x] == PEG and \
                   test_board[y + y0][x + x0] == PEG and \
                   test_board[y + 2 * y0][x + 2 * x0] == HOLE
        except AssertionError:
            print(f"Λανθασμένη λύση (άκυρη κίνηση) {move_index}")
            return False
        flip_hhp(test_board, y, x, y0, x0)
    try:
        assert sum_pegs(test_board) == 1
    except AssertionError:
        print("Λανθασμένη λύση (περισσότεροι από 1 πάσσαλοι στο τέλος)")
        return False
    print("Σωστή λύση")
    return True


def convert_and_write(solution, file_out):
    print(f'Εγγραφή λύσης στο αρχείο: {file_out}')
    f = open(file_out, "w")
    f.write(f'{len(solution)}\n')
    for y, x, y0, x0 in solution:
        f.write(f'{y + 1} {x + 1} {y + 1 + 2 * y0} {x + 1 + 2 * x0}\n')
    f.close()


def create_problem_from_board(board):
    """ Δέχεται τον board ως περιγραφή των διαστάσεων και περιορισμών (WALLs)
        και τον αλλάζει σε επιλύσιμο πρόβλημα (υποθέτοντας ότι αρχικά στον board
        υπάρχουν 0 ή 1 πάσσαλοι."""

    height = len(board)
    width = len(board[0])
    choices = []
    solution = []

    if board.count(PEG) == 0:
        y, x = random.choice([(y, x) for y in range(height)
                              for x in range(width) if board[y][x] != WALL])
        board[y][x] = PEG

    while True:
        for y, row in enumerate(board):
            for x, col in enumerate(row):
                if board[y][x] != HOLE:
                    continue
                else:
                    for y0, x0 in moves:
                        if 0 <= y + 2 * y0 < height and 0 <= x + 2 * x0 < width and \
                                board[y + y0][x + x0] == HOLE and \
                                board[y + 2 * y0][x + 2 * x0] == PEG:
                            choices.append((y, x, y0, x0))
        if choices:
            y, x, y0, x0 = random.choice(choices)
            flip_pph(board, y, x, y0, x0)
            solution.insert(0, (y, x, y0, x0))
            choices.clear()
        else:
            break


def encode_board_to_number(board):
    # κωδικοποίηση του προβλήματος στην ουσία στο 4αδικό σύστημα αρίθμησης
    # με αντιστοίχηση των 0,1,2 στα ψηφία 1,2,3 και για το τέλος γραμμής το 0
    num = 0
    for row in board:
        for x in row:
            num = 4 * num + (x + 1)
        num = 4 * num

    return num


def decode_number_to_board(num):
    # αποκωδικοποίηση του αριθμού με βάση το σχήμα κωδικοποίησης της encode
    answer = []
    while num > 0:
        digit = num % 4
        answer.append(digit)
        num = num // 4
    long = list(reversed(answer))

    si = long.index(0)
    return [[x - 1 for x in y] for y in
            [long[i * (si + 1):(i + 1) * (si + 1) - 1] for i in range(len(long) // (si + 1))]]


def show_code(board):
    print(f'Στο πρόβλημα αντιστοιχεί ο κωδικός: {encode_board_to_number(board)}')


def run_and_write(search_method, board, file_out=None):
    solution = search_method(board)

    if file_out:
        if validate_solution(solution, board):
            convert_and_write(solution, file_out)


def is_valid_board(board):
    return (all([x == WALL or x == PEG or x == HOLE
                 for row in board for x in row]) and
            all([a[0] == a[1] for a in zip([len(x)
                                            for x in board][:], [len(x) for x in board][1:])]))


def pretty_print_solution(solution):
    for move in solution:
        print(move)


def convert_to_project_solution(solution):
    # μετατροπή μεταξύ της δικής μας λύσης στη λύση για την εργασία
    return [(y + 1, x + 1, y + 1 + 2 * y0, x + 1 + 2 * x0)
            for (y, x, y0, x0) in solution]


def pretty_print_chart(chart, algorithms):
    print('-' * (25 * (len(algorithms) + 1) + 1))
    print('Απόλυτοι χρόνοι εκτέλεσης', end='|')
    for a in algorithms:
        print("{:^24}".format(a.__name__), end='|')
    print()
    print('-' * (25 * (len(algorithms) + 1) + 1))

    for time_line in chart:
        print('                         ', end='|')
        # best_time = min(only_times)
        for t in time_line:
            print("{:>24.4f}".format(t), end='|')
        print()

    ratio_times = []
    for time_line in chart:
        best_time = min(time_line)
        ratio_times.append([x / best_time for x in time_line])

    average = [sum(x) / len(x) for x in list(zip(*chart))]
    print('-' * (25 * (len(algorithms) + 1) + 1))
    print('Μ.Ο. χρόνων εκτέλεσης    ', end='|')
    for t in average:
        print("{:>24.4f}".format(t), end='|')
    print()
    print('-' * (25 * (len(algorithms) + 1) + 1))

    print('Σχετικοί χρόνοι εκτέλεσης', end='|')
    for a in algorithms:
        print("{:^24}".format(a.__name__), end='|')
    print()

    for time_line in ratio_times:
        print('                         ', end='|')
        for t in time_line:
            print("{:>24.4f}".format(t), end='|')
        print()

    print('-' * (25 * (len(algorithms) + 1) + 1))
    relative_average = [sum(x) / len(x) for x in list(zip(*ratio_times))]
    print('Μ.Ο. σχετικών χρόνων     ', end='|')
    for t in relative_average:
        print("{:>24.4f}".format(t), end='|')
    print()


def main():
    method = sys.argv[1]

    if method == "depth":  # εκτέλεση DFS (συγκεκριμμένα dfs_recursive)
        file_in = sys.argv[2]
        file_out = sys.argv[3]
        board = get_board_from_file(file_in)
        run_and_write(dfs_recursive, board, file_out)
    elif method == "best":  # εκτέλεση BeFS (συγκεκριμμένα befs_max_exponential)
        file_in = sys.argv[2]
        file_out = sys.argv[3]
        board = get_board_from_file(file_in)
        run_and_write(befs_max_exponential, board, file_out)
    elif method == "check":  # έλεγχος λύσης
        file_in = sys.argv[2]
        file_out = sys.argv[3]
        board = get_board_from_file(file_in)
        # έλεγχος αν για το πρόβλημα του 1ου αρχείου, το 2ο αποτελεί λύση
        pegs, solution = get_solution_from_file(file_out)
        if pegs != len(solution):
            print(f'Το ονομαστικό πλήθος των κινήσεων {pegs} διαφέρει από '
                  f'το πλήθος των κινήσεων που ακολουθούν {len(solution)}.')

        validate_solution(solution, board)

    elif method == "expo":  # Δημιουργία εκ νέου πειραμάτων
        algorithms = [
            dfs_recursive,
            dfs_recursive_random,
            befs_euclidean,
            befs_max_exponential,
            befs_exponential,
            befs_manhattan]

        chart = []
        for file in os.listdir("."):
            if file.startswith("pattern"):
                print(f'Δημιουργία τυχαίων προβλημάτων με βάση το {file}')
                print(f'-----------------------------------------')
                for i in range(5):  # Εκτέλεση 5 φορές για κάθε pattern αρχείο
                    times = []  # για την αποθήκευση των χρόνων εκτέλεσης
                    board = get_board_from_file(file)
                    create_problem_from_board(board)
                    code = encode_board_to_number(board)
                    print(f'Κωδικός προβλήματος: {code}')
                    print(f'-------------------')
                    pretty_print(board)
                    for f in algorithms:
                        print("{:<32}".format(f'Εκτέλεση {f.__name__}' + '...'), end=' ')
                        tic = time.perf_counter()
                        solution = f(board)
                        toc = time.perf_counter()
                        tictoc = toc - tic
                        times.append(tictoc)
                        print(f' χρόνος: ' + "{:>10.4f}".format(tictoc), end=' ')
                        if solution:
                            validate_solution(solution, board)
                            # pretty_print_solution(convert_to_project_solution(solution))
                        else:
                            print('Δεν βρέθηκε λύση')
                    chart.append(times)

            elif file.startswith("problem"):
                times = []  # για την αποθήκευση των χρόνων εκτέλεσης
                print(f'Αρχείο: {file}')
                board = get_board_from_file(file)
                print(f'Κωδικός προβλήματος: {encode_board_to_number(board)}')
                print(f'-------------------')
                pretty_print(board)
                for f in algorithms:
                    print("{:<32}".format(f'Εκτέλεση {f.__name__}' + '...'), end=' ')
                    tic = time.perf_counter()
                    solution = f(board)
                    toc = time.perf_counter()
                    tictoc = toc - tic
                    times.append(tictoc)
                    print(f' χρόνος: ' + "{:>10.4f}".format(tictoc), end=' ')
                    # print(f' χρόνος: {tictoc}', end=' ')
                    if solution:
                        validate_solution(solution, board)
                        # pretty_print_solution(convert_to_project_solution(solution))
                    else:
                        print('Δεν βρέθηκε λύση')
                chart.append(times)
        pretty_print_chart(chart, algorithms)
    elif method == "decode":  # εκτέλεση ενός τυχαίου αλγορίθμου σε κωδικοποιημένο πρόβλημα
        file_out = sys.argv[3]
        number = int(sys.argv[2])
        board = decode_number_to_board(number)
        pretty_print(board)
        algorithms = [
            dfs_recursive,
            dfs_recursive_random,
            befs_euclidean,
            befs_max_exponential,
            befs_exponential,
            befs_manhattan]
        f = random.choice(algorithms)
        print(f'Επιλέχθηκε τυχαία ο αλγόριθμος {f.__name__}')
        run_and_write(f, board, file_out)


main()
