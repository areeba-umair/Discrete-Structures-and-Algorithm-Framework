/**
 * CDAF SYSTEM (Discrete Structures & Graph Algorithms)
 * ====================================================
 * This program implements a comprehensive suite of discrete structure tools:
 * 1. Custom Discrete Set implementation (dynamic arrays, set theory operations).
 * 2. Logic Engine (quantifiers like ForAll, Exists).
 * 3. Graph Theory Engine (Adjacency Matrix/List, Euler, Hamiltonian, MST, Dijkstra).
 * 4. Relations & Functions Analyzer.
 */

 #include <iostream>     // Standard Input/Output streams
 #include <vector>       // Standard vector container
 #include <string>       // String manipulation
 #include <sstream>      // String stream processing
 #include <algorithm>    // Algorithms like sort, swap
 #include <iomanip>      // Input/Output manipulation (setw, etc.)
 #include <queue>        // Priority queue for Dijkstra's algorithm
 
 using namespace std;    // Use the standard namespace to avoid typing std:: repeatedly
 
 // =========================================================
 // PART 0: UTILITIES & CONSTANTS
 // =========================================================
 
 // A constant used to represent "infinity" for shortest path algorithms.
 const int LARGE_VALUE = 1000000000;
 
 // Overload the << operator to print std::pair objects easily (e.g., "(1,2)").
 template<typename T, typename U>
 ostream& operator<<(ostream& output_stream, const pair<T, U>& pair_item) {
     output_stream << "(" << pair_item.first << "," << pair_item.second << ")";
     return output_stream;
 }
 
 // =========================================================
 // PART 1: DISCRETE SET CLASS
 // =========================================================
 // A custom template class representing a mathematical Set.
 // It uses a sorted dynamic array to store unique elements.
 template<typename T>
 class DiscreteSet {
 private:
     T* data_storage;      // Pointer to the dynamic array holding elements
     int storage_capacity; // The current allocated size of the array
     int element_count;    // The actual number of elements currently in the set
 
     // Helper: Doubles the array capacity when it gets full.
     void expand_storage() {
         // If capacity is 0, start with 1, otherwise double it.
         storage_capacity = (storage_capacity == 0) ? 1 : storage_capacity * 2;
         
         // Allocate new memory block
         T* new_storage = new T[storage_capacity];
         
         // Copy existing elements to the new block
         for (int index = 0; index < element_count; index++) 
             new_storage[index] = data_storage[index];
         
         // Free the old memory block to prevent memory leaks
         if (data_storage) delete[] data_storage;
         
         // Point to the new block
         data_storage = new_storage;
     }
 
     // Helper: Binary Search to find the index of a value.
     // Returns index if found, -1 if not found.
     // Complexity: O(log n) because the array is kept sorted.
     int find_element_index(const T& target_value) const {
         if (element_count == 0) return -1;
         int start_index = 0, end_index = element_count - 1;
         while (start_index <= end_index) {
             int middle_index = start_index + (end_index - start_index) / 2;
             if (data_storage[middle_index] == target_value) return middle_index;
             if (data_storage[middle_index] < target_value) start_index = middle_index + 1;
             else end_index = middle_index - 1;
         }
         return -1;
     }
 
 public:
     // Default Constructor: Initializes an empty set.
     DiscreteSet() : data_storage(nullptr), storage_capacity(0), element_count(0) {}
 
     // Copy Constructor: Creates a deep copy of another set.
     // Required because we are managing raw pointers.
     DiscreteSet(const DiscreteSet& other_collection) : data_storage(nullptr), storage_capacity(0), element_count(0) {
         if (other_collection.element_count > 0) {
             storage_capacity = other_collection.element_count;
             element_count = other_collection.element_count;
             data_storage = new T[storage_capacity]; // Allocate own memory
             // Copy data
             for (int index = 0; index < element_count; index++) 
                 data_storage[index] = other_collection.data_storage[index];
         }
     }
 
     // Copy Assignment Operator: Handles "set1 = set2".
     // Prevents self-assignment and memory leaks.
     DiscreteSet& operator=(const DiscreteSet& other_collection) {
         if (this != &other_collection) { // Check for self-assignment
             if (data_storage) delete[] data_storage; // Free existing memory
             
             element_count = other_collection.element_count;
             storage_capacity = other_collection.element_count;
             
             if (element_count > 0) {
                 data_storage = new T[storage_capacity];
                 for (int index = 0; index < element_count; index++) 
                     data_storage[index] = other_collection.data_storage[index];
             }
             else {
                 data_storage = nullptr;
             }
         }
         return *this;
     }
 
     // Destructor: Cleans up memory when the object goes out of scope.
     ~DiscreteSet() { if (data_storage) delete[] data_storage; }
 
     // Inserts a new element while maintaining Sorted Order.
     // Complexity: O(n) due to shifting elements.
     void insert_element(T new_value) {
         if (has_element(new_value)) return; // Sets contain unique elements only
         
         if (element_count == storage_capacity) expand_storage(); // Resize if full
         
         // Find the correct position to keep the array sorted (Insertion Sort logic)
         int insert_position = element_count;
         while (insert_position > 0 && data_storage[insert_position - 1] > new_value) {
             data_storage[insert_position] = data_storage[insert_position - 1]; // Shift right
             insert_position--;
         }
         data_storage[insert_position] = new_value; // Insert
         element_count++;
     }
 
     // Deletes an element if it exists.
     void delete_element(T value_to_remove) {
         int element_position = find_element_index(value_to_remove);
         if (element_position != -1) {
             // Shift all subsequent elements one step left to fill the gap
             for (int index = element_position; index < element_count - 1; ++index) 
                 data_storage[index] = data_storage[index + 1];
             element_count--;
         }
     }
 
     // Resets the set to empty.
     void clear_elements() {
         if (data_storage) delete[] data_storage;
         data_storage = nullptr; element_count = 0; storage_capacity = 0;
     }
 
     // Checks existence using Binary Search.
     bool has_element(T value_to_check) const { return find_element_index(value_to_check) != -1; }
     
     // Getters for size and emptiness.
     int get_count() const { return element_count; }
     bool is_empty() const { return element_count == 0; }
 
     // Safe accessor for elements by index (bounds checked).
     T get_by_index(int index_position) const {
         if (index_position >= 0 && index_position < element_count) return data_storage[index_position];
         return T(); // Return default value if out of bounds
     }
 
     // --- SET OPERATIONS (Set Theory) ---
 
     // Union (A U B): Elements in A OR B.
     // Efficient O(N+M) merge because both arrays are sorted.
     DiscreteSet<T> union_with(const DiscreteSet<T>& other_collection) const {
         DiscreteSet<T> result_collection;
         int index_one = 0, index_two = 0;
         
         // Iterate through both sets simultaneously
         while (index_one < element_count && index_two < other_collection.element_count) {
             if (data_storage[index_one] < other_collection.data_storage[index_two]) 
                 result_collection.insert_element(data_storage[index_one++]);
             else if (other_collection.data_storage[index_two] < data_storage[index_one]) 
                 result_collection.insert_element(other_collection.data_storage[index_two++]);
             else { 
                 // Elements are equal (in both sets), insert once and advance both
                 result_collection.insert_element(data_storage[index_one++]); 
                 index_two++; 
             }
         }
         // Add remaining elements
         while (index_one < element_count) result_collection.insert_element(data_storage[index_one++]);
         while (index_two < other_collection.element_count) result_collection.insert_element(other_collection.data_storage[index_two++]);
         return result_collection;
     }
 
     // Intersection (A n B): Elements in BOTH A AND B.
     DiscreteSet<T> intersect_with(const DiscreteSet<T>& other_collection) const {
         DiscreteSet<T> result_collection;
         int index_one = 0, index_two = 0;
         while (index_one < element_count && index_two < other_collection.element_count) {
             if (data_storage[index_one] < other_collection.data_storage[index_two]) index_one++;
             else if (other_collection.data_storage[index_two] < data_storage[index_one]) index_two++;
             else { 
                 // Match found
                 result_collection.insert_element(data_storage[index_one++]); 
                 index_two++; 
             }
         }
         return result_collection;
     }
 
     // Set Difference (A - B): Elements in A but NOT in B.
     DiscreteSet<T> subtract_set(const DiscreteSet<T>& other_collection) const {
         DiscreteSet<T> result_collection;
         int index_one = 0, index_two = 0;
         while (index_one < element_count && index_two < other_collection.element_count) {
             if (data_storage[index_one] < other_collection.data_storage[index_two]) 
                 result_collection.insert_element(data_storage[index_one++]); // Unique to A
             else if (other_collection.data_storage[index_two] < data_storage[index_one]) 
                 index_two++; // Skip element in B
             else { 
                 // Element exists in both, so discard it (don't add to result)
                 index_one++; index_two++; 
             }
         }
         while (index_one < element_count) result_collection.insert_element(data_storage[index_one++]);
         return result_collection;
     }
 
     // Symmetric Difference (A XOR B): Elements in A or B, but not both.
     // Implementation: (A - B) U (B - A).
     DiscreteSet<T> symmetric_difference(const DiscreteSet<T>& other_collection) const {
         return subtract_set(other_collection).union_with(other_collection.subtract_set(*this));
     }
 
     // Subset Check: Is every element of this set inside 'other_collection'?
     bool is_subset_of(const DiscreteSet<T>& other_collection) const {
         int index_one = 0, index_two = 0;
         while (index_one < element_count && index_two < other_collection.element_count) {
             if (data_storage[index_one] < other_collection.data_storage[index_two]) return false; // Element in A missing from B
             if (data_storage[index_one] == other_collection.data_storage[index_two]) index_one++;
             index_two++;
         }
         return (index_one == element_count); // True if we matched all elements of A
     }
 
     // Proper Subset: Is Subset AND size is strictly smaller.
     bool is_proper_subset_of(const DiscreteSet<T>& other_collection) const {
         return is_subset_of(other_collection) && (element_count < other_collection.element_count);
     }
 
     // Power Set: Generates the set of all subsets.
     // Uses bit manipulation (0 to 2^n - 1) to represent all combinations.
     DiscreteSet<DiscreteSet<T>> generate_power_set() const {
         DiscreteSet<DiscreteSet<T>> power_set_result;
         unsigned long long total_subsets = 1ULL << element_count; // 2^N
         for (unsigned long long mask = 0; mask < total_subsets; mask++) {
             DiscreteSet<T> current_subset;
             for (int bit_position = 0; bit_position < element_count; bit_position++) {
                 // If bit is set, include that element in this subset
                 if (mask & (1ULL << bit_position)) current_subset.insert_element(data_storage[bit_position]);
             }
             power_set_result.insert_element(current_subset);
         }
         return power_set_result;
     }
 
     // Cartesian Product (A x B): Set of all ordered pairs (a, b).
     DiscreteSet<pair<T, T>> cartesian_product(const DiscreteSet<T>& other_collection) const {
         DiscreteSet<pair<T, T>> product_result;
         for (int index_one = 0; index_one < element_count; index_one++) {
             for (int index_two = 0; index_two < other_collection.element_count; index_two++) {
                 product_result.insert_element(make_pair(data_storage[index_one], other_collection.data_storage[index_two]));
             }
         }
         return product_result;
     }
 
     // Comparison Operators (Lexicographical order) for Sets of Sets
     bool operator<(const DiscreteSet<T>& other_collection) const {
         if (element_count != other_collection.element_count) return element_count < other_collection.element_count;
         for (int index = 0; index < element_count; index++) {
             if (data_storage[index] != other_collection.data_storage[index]) return data_storage[index] < other_collection.data_storage[index];
         }
         return false;
     }
     bool operator>(const DiscreteSet<T>& other_collection) const { return other_collection < *this; }
     
     // Equality Operator
     bool operator==(const DiscreteSet<T>& other_collection) const {
         if (element_count != other_collection.element_count) return false;
         for (int index = 0; index < element_count; index++) 
             if (data_storage[index] != other_collection.data_storage[index]) return false;
         return true;
     }
     bool operator!=(const DiscreteSet<T>& other_collection) const { return !(*this == other_collection); }
 
     // Friend function to print the set like "{1,2,3}".
     friend ostream& operator<<(ostream& output_stream, const DiscreteSet<T>& set_to_print) {
         output_stream << "{";
         for (int index = 0; index < set_to_print.element_count; index++) {
             output_stream << set_to_print.data_storage[index];
             if (index < set_to_print.element_count - 1) output_stream << ",";
         }
         output_stream << "}";
         return output_stream;
     }
 };
 
 // =========================================================
 // PART 2: LOGIC & PREDICATES
 // =========================================================
 // Static methods to handle Logical Quantifiers on Sets.
 
 class LogicEngine {
 public:
     // "Exists" Quantifier (∃x P(x))
     template <typename T, typename Condition>
     static bool exists_element(const DiscreteSet<T>& domain_set, Condition test_condition) {
         for (int index = 0; index < domain_set.get_count(); index++) {
             // If at least one element satisfies the condition, return true
             if (test_condition(domain_set.get_by_index(index))) return true;
         }
         return false;
     }
 
     // "For All" Quantifier (∀x P(x))
     template <typename T, typename Condition>
     static bool for_all_elements(const DiscreteSet<T>& domain_set, Condition test_condition) {
         for (int index = 0; index < domain_set.get_count(); index++) {
             // If any element fails the condition, the whole proposition is false
             if (!test_condition(domain_set.get_by_index(index))) return false;
         }
         return true;
     }
 
     // "Unique Existence" (∃!x P(x)) - Exactly one element matches.
     template <typename T, typename Condition>
     static bool exists_unique_element(const DiscreteSet<T>& domain_set, Condition test_condition) {
         int match_count = 0;
         for (int index = 0; index < domain_set.get_count(); index++) {
             if (test_condition(domain_set.get_by_index(index))) match_count++;
         }
         return match_count == 1;
     }
 
     // Verification of De Morgan's Law for Quantifiers:
     // Is ¬(∀x P(x)) equivalent to ∃x ¬P(x)?
     template <typename T, typename Condition>
     static bool verify_negation_for_all(const DiscreteSet<T>& domain, Condition test_condition) {
         auto negated_condition = [&](const T& element) { return !test_condition(element); };
         return !for_all_elements(domain, test_condition) == exists_element(domain, negated_condition);
     }
 
     // Verification of De Morgan's Law for Quantifiers:
     // Is ¬(∃x P(x)) equivalent to ∀x ¬P(x)?
     template <typename T, typename Condition>
     static bool verify_negation_exists(const DiscreteSet<T>& domain, Condition test_condition) {
         auto negated_condition = [&](const T& element) { return !test_condition(element); };
         return !exists_element(domain, test_condition) == for_all_elements(domain, negated_condition);
     }
 };
 
 // =========================================================
 // PART 3: CONSTRAINT BUILDER
 // =========================================================
 // Uses Sets to model real-world constraints (e.g., Network nodes).
 
 class ConstraintCalculator {
 public:
     // Calculate nodes that MUST be included (Critical U High_Priority) - Redundant.
     static DiscreteSet<int> calculate_required_nodes(
         const DiscreteSet<int>& critical_set, const DiscreteSet<int>& high_priority_set, const DiscreteSet<int>& redundant_set)
     {
         return critical_set.union_with(high_priority_set).subtract_set(redundant_set);
     }
 
     // Calculate nodes that cannot be used (Faulty U (All - Required)).
     static DiscreteSet<int> calculate_blocked_nodes(
         const DiscreteSet<int>& universe_set, const DiscreteSet<int>& required_set, const DiscreteSet<int>& faulty_set)
     {
         return faulty_set.union_with(universe_set.subtract_set(required_set));
     }
 
     // Verifies if a list of sets covers the entire "Universe" set.
     static bool verify_coverage(const DiscreteSet<int>& full_universe, const vector<DiscreteSet<int>>& covering_collections) {
         DiscreteSet<int> combined_set;
         // Union all covering sets together
         for (size_t index = 0; index < covering_collections.size(); ++index) 
             combined_set = combined_set.union_with(covering_collections[index]);
         
         // Check if Combined == Universe
         return full_universe.is_subset_of(combined_set) && combined_set.is_subset_of(full_universe);
     }
 };
 
 // =========================================================
 // PART 4: NETWORK GRAPH
 // =========================================================
 // Represents a graph using both Adjacency Matrix and Adjacency List.
 
 class NetworkStructure {
 private:
     int node_quantity;      // Number of vertices
     int edge_quantity;      // Number of edges
     
     // Adjacency Matrix: O(1) lookup, O(V^2) space.
     vector<vector<int>> connection_matrix;
     
     // Adjacency List: Space efficient, good for iteration. Pairs store {neighbor, weight}.
     vector<vector<pair<int, int>>> adjacency_lists;
     
     bool directed_flag;     // True if graph is directed (A->B != B->A)
 
     // Recursive Helper for Hamiltonian Path (Backtracking)
     bool find_hamiltonian_path(vector<int>& current_path, vector<bool>& visited_nodes, int current_position) const {
         // Base Case: All nodes are included in the path
         if (current_position == node_quantity) {
             // Check if there is an edge back to start (for Cycle)
             if (directed_flag) return connection_matrix[current_path[current_position - 1]][current_path[0]] != 0;
             return connection_matrix[current_path[current_position - 1]][current_path[0]] != 0 || connection_matrix[current_path[0]][current_path[current_position - 1]] != 0;
         }
 
         // Try every vertex as the next candidate
         for (int next_node = 1; next_node < node_quantity; next_node++) {
             bool is_connected = (connection_matrix[current_path[current_position - 1]][next_node] != 0);
             
             if (!visited_nodes[next_node] && is_connected) {
                 // Choose
                 current_path[current_position] = next_node; 
                 visited_nodes[next_node] = true;
                 
                 // Explore
                 if (find_hamiltonian_path(current_path, visited_nodes, current_position + 1)) return true;
                 
                 // Un-choose (Backtrack)
                 visited_nodes[next_node] = false; 
                 current_path[current_position] = -1;
             }
         }
         return false;
     }
 
     // Helper: Depth First Search (DFS) to find connected components
     void traverse_depth_first(int current_node, vector<bool>& visited_nodes) const {
         visited_nodes[current_node] = true;
         for (size_t index = 0; index < adjacency_lists[current_node].size(); ++index) {
             if (!visited_nodes[adjacency_lists[current_node][index].first]) 
                 traverse_depth_first(adjacency_lists[current_node][index].first, visited_nodes);
         }
     }
 
 public:
     // Constructor
     NetworkStructure(int total_nodes, bool directed = false) : node_quantity(total_nodes), directed_flag(directed), edge_quantity(0) {
         connection_matrix.resize(total_nodes, vector<int>(total_nodes, 0));
         adjacency_lists.resize(total_nodes);
     }
 
     // Add an edge between two nodes with a weight
     void add_edge(int source_node, int target_node, int edge_weight) {
         if (source_node >= node_quantity || target_node >= node_quantity) return; // Bounds check
         
         // Update Matrix
         if (connection_matrix[source_node][target_node] == 0) edge_quantity++;
         connection_matrix[source_node][target_node] = edge_weight;
 
         // Update Adjacency List (Handle duplicates by updating weight)
         bool found_existing = false;
         for (size_t index = 0; index < adjacency_lists[source_node].size(); ++index) {
             if (adjacency_lists[source_node][index].first == target_node) {
                 adjacency_lists[source_node][index].second = edge_weight; 
                 found_existing = true; 
                 break;
             }
         }
         if (!found_existing) adjacency_lists[source_node].push_back(make_pair(target_node, edge_weight));
 
         // If Undirected, mirror the edge
         if (!directed_flag) {
             connection_matrix[target_node][source_node] = edge_weight;
             found_existing = false;
             for (size_t index = 0; index < adjacency_lists[target_node].size(); ++index) {
                 if (adjacency_lists[target_node][index].first == source_node) {
                     adjacency_lists[target_node][index].second = edge_weight; 
                     found_existing = true; 
                     break;
                 }
             }
             if (!found_existing) adjacency_lists[target_node].push_back(make_pair(source_node, edge_weight));
         }
     }
 
     // Removes an edge from the graph
     void remove_edge(int source_node, int target_node) {
         if (source_node >= node_quantity || target_node >= node_quantity) return;
         
         // Zero out matrix entry
         connection_matrix[source_node][target_node] = 0;
         
         // Erase from vector
         for (auto list_iterator = adjacency_lists[source_node].begin(); list_iterator != adjacency_lists[source_node].end(); ++list_iterator) {
             if (list_iterator->first == target_node) { adjacency_lists[source_node].erase(list_iterator); break; }
         }
         
         // Handle undirected mirror
         if (!directed_flag) {
             connection_matrix[target_node][source_node] = 0;
             for (auto list_iterator = adjacency_lists[target_node].begin(); list_iterator != adjacency_lists[target_node].end(); ++list_iterator) {
                 if (list_iterator->first == source_node) { adjacency_lists[target_node].erase(list_iterator); break; }
             }
         }
     }
 
     // Check if edge exists
     bool edge_exists(int source_node, int target_node) const {
         if (source_node >= node_quantity || target_node >= node_quantity) return false;
         return connection_matrix[source_node][target_node] != 0;
     }
 
     int get_edge_weight(int source_node, int target_node) const {
         if (source_node >= node_quantity || target_node >= node_quantity) return 0;
         return connection_matrix[source_node][target_node];
     }
 
     int get_node_count() const { return node_quantity; }
     const vector<vector<pair<int, int>>>& get_adjacency() const { return adjacency_lists; }
 
     // Check if Graph is Complete (Every node connects to every other node)
     bool is_complete() const {
         int expected_edges = node_quantity * (node_quantity - 1) / 2;
         int actual_edges = 0;
         for (int index = 0; index < node_quantity; ++index) actual_edges += adjacency_lists[index].size();
         if (!directed_flag) actual_edges /= 2;
         return actual_edges == expected_edges;
     }
 
     // Euler Circuit: Start at A, visit every EDGE exactly once, return to A.
     // Condition (Undirected): Graph connected + All vertices have EVEN degree.
     bool has_euler_circuit() const {
         if (node_quantity == 0) return false;
         for (const auto& neighbor_list : adjacency_lists) 
             if (neighbor_list.size() % 2 != 0) return false; // Odd degree found
         return true;
     }
 
     // Euler Path: Visit every EDGE exactly once (start/end can differ).
     // Condition: 0 or 2 vertices have odd degrees.
     bool has_euler_trail() const {
         int odd_degree_nodes = 0;
         for (const auto& neighbor_list : adjacency_lists) 
             if (neighbor_list.size() % 2 != 0) odd_degree_nodes++;
         return (odd_degree_nodes == 0 || odd_degree_nodes == 2);
     }
 
     // Hamiltonian Cycle: Visit every VERTEX exactly once, return to start.
     // Condition: NP-Complete problem, solved here via backtracking.
     bool contains_hamiltonian_cycle() const {
         if (node_quantity == 0) return false;
         vector<int> path_nodes(node_quantity, -1);
         vector<bool> visited_nodes(node_quantity, false);
         
         path_nodes[0] = 0; // Start at node 0
         visited_nodes[0] = true;
         
         return find_hamiltonian_path(path_nodes, visited_nodes, 1);
     }
 
     // Count Connected Components using repeated DFS
     int count_components() const {
         int component_count = 0;
         vector<bool> visited_nodes(node_quantity, false);
         for (int node_index = 0; node_index < node_quantity; node_index++) {
             if (!visited_nodes[node_index]) { 
                 traverse_depth_first(node_index, visited_nodes); 
                 component_count++; 
             }
         }
         return component_count;
     }
 
     // Print the matrix to console
     void display_matrix() const {
         cout << "\nAdjacency Matrix:\n";
         for (int row = 0; row < node_quantity; ++row) {
             cout << "[ ";
             for (int col = 0; col < node_quantity; ++col) cout << setw(2) << connection_matrix[row][col] << " ";
             cout << "]\n";
         }
     }
 
     // Prints a summary of graph properties
     void generate_properties_report() const {
         int total_edges = 0;
         for (int index = 0; index < node_quantity; ++index) total_edges += adjacency_lists[index].size();
         if (!directed_flag) total_edges /= 2;
 
         cout << "\nNETWORK GRAPH PROPERTIES\n";
         cout << "========================\n";
         cout << "Total Vertices: [" << node_quantity << "]\n";
         cout << "Total Edges:    [" << total_edges << "]\n";
         cout << "Graph Type:     [" << (directed_flag ? "DIRECTED" : "UNDIRECTED") << "]\n";
         cout << "Euler Circuit Exists:     [" << (has_euler_circuit() ? "TRUE" : "FALSE") << "]\n";
         cout << "Euler Path Exists:        [" << (has_euler_trail() ? "TRUE" : "FALSE") << "]\n";
         cout << "Hamiltonian Cycle Exists: [" << (contains_hamiltonian_cycle() ? "TRUE" : "FALSE") << "]\n";
         cout << "Complete Graph:           [" << (is_complete() ? "TRUE" : "FALSE") << "]\n";
         cout << "Connected Components:     [" << count_components() << "]\n";
         cout << "========================\n";
     }
 };
 
 // =========================================================
 // PART 5: GRAPH ALGORITHMS
 // =========================================================
 
 // Struct to hold result of MST Calculation
 struct SpanningTreeResult {
     vector<pair<int, pair<int, int>>> selected_edges; // List of edges in MST
     int total_cost;
     bool successful; // False if graph is disconnected relative to required nodes
 };
 
 // Edge structure for Kruskal's Algorithm sorting
 struct GraphConnection { 
     int node_a, node_b, weight_value; 
     // Overload < operator for sorting by weight
     bool operator<(const GraphConnection& other_connection) const { 
         return weight_value < other_connection.weight_value; 
     } 
 };
 
 // Disjoint Set Union (DSU) / Union-Find data structure
 // Used to detect cycles in Kruskal's Algorithm
 struct UnionFindStructure {
     vector<int> parent_array;
     UnionFindStructure(int node_count) { 
         parent_array.resize(node_count); 
         for (int index = 0; index < node_count; index++) parent_array[index] = index; // Each node is its own parent initially
     }
     // Find representative with Path Compression
     int find_set(int node_index) { 
         return (parent_array[node_index] == node_index) ? node_index : parent_array[node_index] = find_set(parent_array[node_index]); 
     }
     // Union two sets
     void union_sets(int node_a, int node_b) { 
         parent_array[find_set(node_a)] = find_set(node_b); 
     }
 };
 
 class GraphAlgorithmExecutor {
 public:
     // KRUSKAL'S ALGORITHM for Minimum Spanning Tree (MST)
     // + Verification that specific "Required Nodes" are connected.
     static SpanningTreeResult compute_minimum_spanning_tree(const NetworkStructure& graph_input, const DiscreteSet<int>& required_nodes) {
         SpanningTreeResult tree_result; tree_result.total_cost = 0; tree_result.successful = true;
         int vertex_total = graph_input.get_node_count();
         vector<GraphConnection> connection_list;
 
         // 1. Extract all edges
         for (int row = 0; row < vertex_total; row++) {
             for (int col = row + 1; col < vertex_total; col++) {
                 int weight_val = graph_input.get_edge_weight(row, col);
                 if (weight_val > 0) connection_list.push_back({ row, col, weight_val });
             }
         }
         // 2. Sort edges by weight (Ascending)
         sort(connection_list.begin(), connection_list.end());
 
         // 3. Process edges
         UnionFindStructure union_structure(vertex_total);
         for (size_t index = 0; index < connection_list.size(); ++index) {
             GraphConnection current_connection = connection_list[index];
             
             // If nodes are in different sets, add edge (no cycle created)
             if (union_structure.find_set(current_connection.node_a) != union_structure.find_set(current_connection.node_b)) {
                 union_structure.union_sets(current_connection.node_a, current_connection.node_b);
                 tree_result.selected_edges.push_back(make_pair(current_connection.node_a, make_pair(current_connection.node_b, current_connection.weight_value)));
                 tree_result.total_cost += current_connection.weight_value;
             }
         }
 
         // 4. Verify connectivity for Required Nodes
         if (required_nodes.get_count() > 0) {
             int reference_root = union_structure.find_set(required_nodes.get_by_index(0));
             for (int index = 1; index < required_nodes.get_count(); index++) {
                 // If any required node has a different root, the graph is disconnected for these nodes
                 if (union_structure.find_set(required_nodes.get_by_index(index)) != reference_root) tree_result.successful = false;
             }
         }
         return tree_result;
     }
 
     // DIJKSTRA'S ALGORITHM for Shortest Path
     static void find_shortest_distance(const NetworkStructure& graph_input, int start_node, int end_node) {
         int vertex_total = graph_input.get_node_count();
         if (start_node >= vertex_total || end_node >= vertex_total) { cout << "Invalid vertices.\n"; return; }
 
         vector<int> distance_array(vertex_total, LARGE_VALUE); // initialize distances to infinity
         vector<int> predecessor_array(vertex_total, -1);       // store path
         distance_array[start_node] = 0;
 
         // Min-Priority Queue: stores {distance, node_index}
         priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> priority_queue;
         priority_queue.push(make_pair(0, start_node));
 
         const auto& adjacency_structure = graph_input.get_adjacency();
 
         while (!priority_queue.empty()) {
             int current_node = priority_queue.top().second;
             int current_distance = priority_queue.top().first;
             priority_queue.pop();
 
             // Optimization: If we found a shorter path previously, skip this outdated entry
             if (current_distance > distance_array[current_node]) continue;
             if (current_node == end_node) break; // Optimization: stop if target reached
 
             // Relax Edges
             for (size_t index = 0; index < adjacency_structure[current_node].size(); ++index) {
                 int neighbor_node = adjacency_structure[current_node][index].first;
                 int edge_weight = adjacency_structure[current_node][index].second;
                 
                 // If path through current_node is shorter...
                 if (distance_array[current_node] + edge_weight < distance_array[neighbor_node]) {
                     distance_array[neighbor_node] = distance_array[current_node] + edge_weight;
                     predecessor_array[neighbor_node] = current_node;
                     priority_queue.push(make_pair(distance_array[neighbor_node], neighbor_node));
                 }
             }
         }
 
         // Output Result
         if (distance_array[end_node] != LARGE_VALUE) {
             cout << "Shortest Path Cost: " << distance_array[end_node] << "\nPath: [";
             vector<int> path_nodes;
             int current_node = end_node;
             // Backtrack from end to start to reconstruct path
             while (current_node != -1) { path_nodes.push_back(current_node); current_node = predecessor_array[current_node]; }
             for (int index = path_nodes.size() - 1; index >= 0; index--) cout << path_nodes[index] << (index > 0 ? "->" : "");
             cout << "]\n";
         }
         else {
             cout << "No path found.\n";
         }
     }
 };
 
 // =========================================================
 // PART 6: RELATIONS & FUNCTIONS
 // =========================================================
 
 class BinaryRelationStructure {
     DiscreteSet<int> relation_domain;
     vector<pair<int, int>> relation_pairs; // Stores relations as pairs (a,b)
 public:
     BinaryRelationStructure(const DiscreteSet<int>& domain_set) : relation_domain(domain_set) {}
     void add_relation_pair(int first_element, int second_element) { relation_pairs.push_back(make_pair(first_element, second_element)); }
 
     // Reflexive: For every 'a' in Domain, (a,a) must exist in relation.
     bool is_reflexive() const {
         for (int index = 0; index < relation_domain.get_count(); index++) {
             bool found_pair = false;
             int domain_element = relation_domain.get_by_index(index);
             // Search for (a,a)
             for (size_t pair_index = 0; pair_index < relation_pairs.size(); ++pair_index)
                 if (relation_pairs[pair_index].first == domain_element && relation_pairs[pair_index].second == domain_element) found_pair = true;
             if (!found_pair) return false;
         }
         return true;
     }
     
     // Symmetric: If (a,b) exists, (b,a) must exist.
     bool is_symmetric() const {
         for (size_t index = 0; index < relation_pairs.size(); ++index) {
             bool has_mirror = false;
             for (size_t jndex = 0; jndex < relation_pairs.size(); ++jndex)
                 if (relation_pairs[jndex].first == relation_pairs[index].second && relation_pairs[jndex].second == relation_pairs[index].first) has_mirror = true;
             if (!has_mirror) return false;
         }
         return true;
     }
 };
 
 class DiscreteFunctionStructure {
     DiscreteSet<int> function_domain, function_codomain;
     vector<pair<int, int>> function_mapping;
 public:
     DiscreteFunctionStructure(DiscreteSet<int> domain_set, DiscreteSet<int> codomain_set) : function_domain(domain_set), function_codomain(codomain_set) {}
 
     void define_mapping(int input_value, int output_value) {
         // Update existing mapping if input already exists (functions have unique outputs for inputs)
         for (size_t index = 0; index < function_mapping.size(); ++index) {
             if (function_mapping[index].first == input_value) { function_mapping[index].second = output_value; return; }
         }
         function_mapping.push_back(make_pair(input_value, output_value));
     }
 
     // Total Function: Every element in Domain has a mapping.
     bool is_total_function() const { return function_mapping.size() == (size_t)function_domain.get_count(); }
 
     // Injective (One-to-One): No two inputs map to the same output.
     bool is_injective() const {
         DiscreteSet<int> output_values;
         for (size_t index = 0; index < function_mapping.size(); ++index) {
             if (output_values.has_element(function_mapping[index].second)) return false; // Duplicate output found
             output_values.insert_element(function_mapping[index].second);
         }
         return true;
     }
 
     // Bijective: Injective + Surjective (covered by Size checks usually in finite sets).
     bool is_bijective() const { return is_injective() && (function_mapping.size() == (size_t)function_domain.get_count()); }
 };
 
 // =========================================================
 // PART 7: INTERACTIVE CONTROLLER
 // =========================================================
 // Handles User Interface and Menu Navigation
 
 class SystemController {
 private:
     DiscreteSet<int> collection_a, collection_b; // General purpose sets for Demo
     NetworkStructure* graph_instance; // Pointer to current graph
     // Specialized sets for logic module
     DiscreteSet<int> critical_nodes, high_nodes, redundant_nodes, faulty_nodes, all_nodes_set;
 
     // Sub-menu for editing a specific set
     void modify_collection(DiscreteSet<int>& target_collection, string collection_name) {
         int user_choice, element_value;
         do {
             cout << "\n--- EDIT SET " << collection_name << " ---\n";
             cout << "Current Set: " << target_collection << " (Size: " << target_collection.get_count() << ")\n";
             cout << "1. Add Element\n";
             cout << "2. Delete Element\n";
             cout << "3. Check Membership\n";
             cout << "4. Clear Set\n";
             cout << "5. Check if Empty\n";
             cout << "0. Back\nOption: ";
 
             // Validate Input
             if (!(cin >> user_choice)) { cin.clear(); cin.ignore(1000, '\n'); continue; }
 
             switch (user_choice) {
             case 1: { cout << "Enter value: "; cin >> element_value; target_collection.insert_element(element_value); break; }
             case 2: { cout << "Enter value: "; cin >> element_value; target_collection.delete_element(element_value); break; }
             case 3: {
                 cout << "Enter value: "; cin >> element_value;
                 if (target_collection.has_element(element_value)) cout << element_value << " IS a member.\n";
                 else cout << element_value << " is NOT a member.\n";
                 break;
             }
             case 4: { target_collection.clear_elements(); cout << "Set Cleared.\n"; break; }
             case 5: { cout << (target_collection.is_empty() ? "Set is Empty.\n" : "Set has elements.\n"); break; }
             }
         } while (user_choice != 0);
     }
 
     // Module 1: Set Operations Interface
     void handle_set_operations() {
         int user_choice;
         // Lambda for predicate testing (x > 4)
         auto greater_than_four = [](const int& element) { return element > 4; };
 
         do {
             cout << "\n--- SET OPERATIONS ---\n";
             cout << "Status -> A: " << collection_a << " | B: " << collection_b << "\n";
             cout << "1. Edit Set A\n2. Edit Set B\n3. Union\n4. Intersection\n5. Difference\n6. Symmetric Diff\n";
             cout << "7. Subset Checks\n8. Power Set A\n9. Cartesian Product\n";
             cout << "10. Logic: ForAll/Exists/Unique (x > 4)\n11. Verify Logic Laws\n0. Back\nSelect: ";
 
             if (!(cin >> user_choice)) { cin.clear(); cin.ignore(1000, '\n'); continue; }
 
             switch (user_choice) {
             case 1: { modify_collection(collection_a, "A"); break; }
             case 2: { modify_collection(collection_b, "B"); break; }
             case 3: { cout << ">> Result: " << collection_a.union_with(collection_b) << "\n"; break; }
             case 4: { cout << ">> Result: " << collection_a.intersect_with(collection_b) << "\n"; break; }
             case 5: { cout << ">> Result: " << collection_a.subtract_set(collection_b) << "\n"; break; }
             case 6: { cout << ">> Result: " << collection_a.symmetric_difference(collection_b) << "\n"; break; }
             case 7: {
                 cout << "A subset of B? " << (collection_a.is_subset_of(collection_b) ? "YES" : "NO") << "\n";
                 cout << "A strict subset B? " << (collection_a.is_proper_subset_of(collection_b) ? "YES" : "NO") << "\n";
                 break;
             }
             case 8: { cout << ">> Powerset A: " << collection_a.generate_power_set() << "\n"; break; }
             case 9: { cout << ">> Cartesian: " << collection_a.cartesian_product(collection_b) << "\n"; break; }
             case 10: {
                 // Testing predicates
                 cout << "ForAll (x>4): " << (LogicEngine::for_all_elements(collection_a, greater_than_four) ? "True" : "False") << "\n";
                 cout << "Exists (x>4): " << (LogicEngine::exists_element(collection_a, greater_than_four) ? "True" : "False") << "\n";
                 cout << "Unique (x>4): " << (LogicEngine::exists_unique_element(collection_a, greater_than_four) ? "True" : "False") << "\n";
                 break;
             }
             case 11: {
                 // Testing De Morgan's Laws
                 bool verification_one = LogicEngine::verify_negation_for_all(collection_a, greater_than_four);
                 bool verification_two = LogicEngine::verify_negation_exists(collection_a, greater_than_four);
                 cout << "1. Not(ForAll) == Exists(Not): " << (verification_one ? "VERIFIED" : "FAILED") << "\n";
                 cout << "2. Not(Exists) == ForAll(Not): " << (verification_two ? "VERIFIED" : "FAILED") << "\n";
                 break;
             }
             }
         } while (user_choice != 0);
     }
 
     // Helper to bulk read a set from console
     DiscreteSet<int> read_collection(string collection_name) {
         DiscreteSet<int> new_collection;
         cout << "Enter elements for " << collection_name << " (enter -1 to stop): ";
         int element_value;
         while (cin >> element_value && element_value != -1) new_collection.insert_element(element_value);
         return new_collection;
     }
 
     // Module 2: Graph Operations Interface
     void handle_graph_operations() {
         int user_choice, node_one, node_two, weight_value;
         do {
             cout << "\n--- GRAPH MODULE (Granular Control) ---\n";
             if (graph_instance) cout << "Graph Active: " << graph_instance->get_node_count() << " Vertices.\n";
             else cout << "NO GRAPH CREATED.\n";
 
             cout << "1. Create New Graph\n2. Insert Edge\n3. Delete Edge\n4. Show Adjacency Matrix\n";
             cout << "5. Generate Full Report\n";
             cout << "6. Run MST (with Mandatory Check)\n7. Run Shortest Path (Dijkstra)\n";
             cout << "--------------------------------\n";
             cout << "8. Check Euler Circuit\n";
             cout << "9. Check Euler Path\n";
             cout << "10. Check Hamiltonian Cycle\n";
             cout << "11. Count Connected Components\n";
             cout << "12. Check Graph Completeness\n";
             cout << "0. Back\nOption: ";
 
             if (!(cin >> user_choice)) { cin.clear(); cin.ignore(1000, '\n'); continue; }
 
             switch (user_choice) {
             case 1: {
                 cout << "Num Vertices: "; cin >> node_one;
                 if (graph_instance) delete graph_instance; // Avoid memory leak
                 graph_instance = new NetworkStructure(node_one);
                 cout << "Graph Created.\n";
                 break;
             }
             case 2: {
                 if (!graph_instance) { cout << "Create graph first.\n"; break; }
                 cout << "From To Weight: "; cin >> node_one >> node_two >> weight_value;
                 graph_instance->add_edge(node_one, node_two, weight_value);
                 break;
             }
             case 3: {
                 if (!graph_instance) { cout << "Create graph first.\n"; break; }
                 cout << "From To: "; cin >> node_one >> node_two;
                 graph_instance->remove_edge(node_one, node_two);
                 break;
             }
             case 4: { if (graph_instance) graph_instance->display_matrix(); break; }
             case 5: { if (graph_instance) graph_instance->generate_properties_report(); break; }
             case 6: {
                 if (!graph_instance) break;
                 // Calculate required nodes from Logic Module data
                 DiscreteSet<int> mandatory_nodes = ConstraintCalculator::calculate_required_nodes(critical_nodes, high_nodes, redundant_nodes);
                 cout << "Mandatory Nodes: " << mandatory_nodes << "\n";
 
                 cout << "\nMINIMUM SPANNING TREE (Kruskal's):\n";
                 SpanningTreeResult tree_result = GraphAlgorithmExecutor::compute_minimum_spanning_tree(*graph_instance, mandatory_nodes);
                 
                 for (size_t index = 0; index < tree_result.selected_edges.size(); ++index)
                     cout << "Edge (" << tree_result.selected_edges[index].first << ", " << tree_result.selected_edges[index].second.first << "): Weight " << tree_result.selected_edges[index].second.second << "\n";
                 cout << "TOTAL COST: " << tree_result.total_cost << "\n";
                 cout << "RESULT: " << (tree_result.successful ? "SUCCESS" : "FAILURE") << "\n";
                 break;
             }
             case 7: {
                 if (!graph_instance) break;
                 cout << "Start End: "; cin >> node_one >> node_two;
                 GraphAlgorithmExecutor::find_shortest_distance(*graph_instance, node_one, node_two);
                 break;
             }
             case 8: {
                 if (graph_instance) cout << "Euler Circuit: " << (graph_instance->has_euler_circuit() ? "YES" : "NO") << "\n";
                 break;
             }
             case 9: {
                 if (graph_instance) cout << "Euler Path: " << (graph_instance->has_euler_trail() ? "YES" : "NO") << "\n";
                 break;
             }
             case 10: {
                 if (graph_instance) cout << "Hamiltonian Cycle: " << (graph_instance->contains_hamiltonian_cycle() ? "YES" : "NO") << "\n";
                 break;
             }
             case 11: {
                 if (graph_instance) cout << "Connected Components: " << graph_instance->count_components() << "\n";
                 break;
             }
             case 12: {
                 if (graph_instance) cout << "Is Complete Graph: " << (graph_instance->is_complete() ? "YES" : "NO") << "\n";
                 break;
             }
             }
         } while (user_choice != 0);
     }
 
     // Module 3: Logic & Constraints Interface
     void handle_constraints() {
         int user_choice;
         do {
             cout << "\n--- LOGIC & CONSTRAINTS ---\n";
             cout << "1. Set Critical/High/Redundant Nodes\n";
             cout << "2. Set Faulty Nodes\n";
             cout << "3. Test Coverage/Forbidden\n";
             cout << "4. Show Mandatory Nodes\n";
             cout << "0. Back\nOption: ";
 
             if (!(cin >> user_choice)) { cin.clear(); cin.ignore(1000, '\n'); continue; }
 
             switch (user_choice) {
             case 1: {
                 critical_nodes = read_collection("Critical Infrastructure");
                 high_nodes = read_collection("High Traffic");
                 redundant_nodes = read_collection("Redundancy Nodes");
                 break;
             }
             case 2: {
                 faulty_nodes = read_collection("Faulty Nodes");
                 all_nodes_set = read_collection("All Nodes Universe");
                 break;
             }
             case 3: {
                 // Complex set algebra: (Critical U High) - Redundant
                 DiscreteSet<int> mandatory_nodes = ConstraintCalculator::calculate_required_nodes(critical_nodes, high_nodes, redundant_nodes);
                 // (All - Required) U Faulty
                 DiscreteSet<int> blocked_nodes = ConstraintCalculator::calculate_blocked_nodes(all_nodes_set, mandatory_nodes, faulty_nodes);
                 cout << "Forbidden Nodes: " << blocked_nodes << "\n";
 
                 vector<DiscreteSet<int>> coverage_sets;
                 coverage_sets.push_back(critical_nodes); coverage_sets.push_back(high_nodes);
                 bool coverage_result = ConstraintCalculator::verify_coverage(all_nodes_set, coverage_sets);
                 cout << "Verify Coverage (Critical+High == All?): " << (coverage_result ? "YES" : "NO") << "\n";
                 break;
             }
             case 4: {
                 DiscreteSet<int> mandatory_nodes = ConstraintCalculator::calculate_required_nodes(critical_nodes, high_nodes, redundant_nodes);
                 cout << ">>> MANDATORY NODES: " << mandatory_nodes << "\n";
                 break;
             }
             }
         } while (user_choice != 0);
     }
 
     // Module 4: Relations Interface
     void handle_relations() {
         cout << "\n--- RELATIONS ---\n";
         DiscreteSet<int> domain_collection = read_collection("Domain");
         BinaryRelationStructure relation_object(domain_collection);
         
         cout << "Enter pairs (u v), -1 -1 to stop:\n";
         int first_value, second_value;
         while (cin >> first_value >> second_value && first_value != -1) 
             relation_object.add_relation_pair(first_value, second_value);
 
         cout << "Reflexive: " << (relation_object.is_reflexive() ? "Yes" : "No") << "\n";
         cout << "Symmetric: " << (relation_object.is_symmetric() ? "Yes" : "No") << "\n";
     }
 
 public:
     SystemController() : graph_instance(nullptr) {}
     
     // Main Loop
     void execute_program() {
         int user_choice;
         do {
             cout << "\n=== CDAF INTERACTIVE SYSTEM (v15.0) ===\n";
             cout << "1. Set Operations Module\n";
             cout << "2. Graph Algorithms Module\n";
             cout << "3. Logic & Constraints Module\n";
             cout << "4. Relations Analyzer\n";
             cout << "5. Run Full Integrated Analysis (Sequence)\n";
             cout << "0. Exit\n";
             cout << "Select Module: ";
 
             if (!(cin >> user_choice)) { cin.clear(); cin.ignore(1000, '\n'); continue; }
 
             switch (user_choice) {
             case 1: { handle_set_operations(); break; }
             case 2: { handle_graph_operations(); break; }
             case 3: { handle_constraints(); break; }
             case 4: { handle_relations(); break; }
             case 5: {
                 // Integration Test: Combines Sets and Graphs
                 if (!graph_instance) { cout << "No graph! Create one in Module 2 first.\n"; break; }
                 cout << "\n--- FULL INTEGRATION SEQUENCE ---\n";
                 
                 // 1. Calculate Required nodes via Set Logic
                 DiscreteSet<int> mandatory_nodes = ConstraintCalculator::calculate_required_nodes(critical_nodes, high_nodes, redundant_nodes);
                 cout << "1. Mandatory Nodes: " << mandatory_nodes << "\n";
 
                 // 2. Compute MST considering these nodes
                 cout << "2. MST Analysis:\n";
                 SpanningTreeResult tree_result = GraphAlgorithmExecutor::compute_minimum_spanning_tree(*graph_instance, mandatory_nodes);
                 cout << "   Cost: " << tree_result.total_cost << " | Success: " << (tree_result.successful ? "Yes" : "No") << "\n";
 
                 // 3. Report Graph Topology
                 cout << "3. Graph Properties:\n";
                 graph_instance->generate_properties_report();
                 break;
             }
             }
         } while (user_choice != 0);
     }
 };
 
 // Entry Point
 int main() {
     SystemController application;
     application.execute_program();
     return 0;
 }
