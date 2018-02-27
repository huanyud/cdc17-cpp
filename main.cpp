#include <iostream>
#include <ctime>
#include <chrono>
// C++ STL
#include <string>
#include <unordered_map>
#include <queue>
#include <unordered_set>
#include <vector>
// LEMON
#include <lemon/smart_graph.h>
#include <lemon/network_simplex.h>
#include <lemon/cost_scaling.h>
#include <lemon/capacity_scaling.h>
#include <lemon/cycle_canceling.h>

using namespace std;
using namespace lemon;

// Global variables
SmartDigraph g;
unordered_map<string, int> name_id_map;
SmartDigraph::NodeMap<string> node_name(g);
SmartDigraph::ArcMap<int> capacity_map(g);
SmartDigraph::ArcMap<double> weight_map(g);
SmartDigraph::NodeMap<int> supply_map(g);

// Build a Lemon graph given graph parameters
void build_graph(int num_of_source, int num_of_sink, double arc_prob, 
                 int supply_each, double prior_prob[], double detect_prob[])
{
    // Add source nodes
    for (int i = 0; i < num_of_source; i++) {
        SmartDigraph::Node node = g.addNode();
        // Record node ID given node name in string
        name_id_map["s" + to_string(i)] = g.id(node);
        // Record node name in string
        node_name[node] = "s" + to_string(i);
        // Set supply
        supply_map[node] = supply_each;
    }
    // Add sink nodes
    for (int i = 0; i < num_of_sink; i++) {
        SmartDigraph::Node node = g.addNode();
        // Record node ID given node name in string
        name_id_map["t" + to_string(i)] = g.id(node);
        // Record node name in string
        node_name[node] = "t" + to_string(i);
    }
    // Add global sink
    SmartDigraph::Node gt = g.addNode();
    name_id_map["gt"] = g.id(gt);
    // Record global sink name in string
    node_name[gt] = "gt";
    // Set demand at global sink
    supply_map[gt] = -supply_each * num_of_source;
    // Add arcs between sources and sinks
    std::mt19937 gen(1);
    std::uniform_real_distribution<> dis(0, 1);
    for (int i = 0; i < num_of_source; i++) {
        for (int j = 0; j < num_of_sink; j++) {
            if (dis(gen) > arc_prob) {
                SmartDigraph::Node source = SmartDigraph::nodeFromId(name_id_map["s" + to_string(i)]);
                SmartDigraph::Node sink   = SmartDigraph::nodeFromId(name_id_map["t" + to_string(j)]);
                SmartDigraph::Arc arc = g.addArc(source, sink);
                // Record arc ID given arc name in string
                name_id_map["s" + to_string(i) + "t" + to_string(j)] = g.id(arc);
                // Set capacity
                capacity_map[arc] = supply_map[source];
            }
        }
    }
    // Check if every source is connected to at least one sink
    for (int i = 0; i < num_of_source; i++) {
        SmartDigraph::Node source = SmartDigraph::nodeFromId(name_id_map["s" + to_string(i)]);
        SmartDigraph::OutArcIt a(g, source); 
        if (a == INVALID) {
            cout << "Node s" << i << " is not connected;" << endl;
            // Randomly connect it to some sink
            int rnd = rand() % num_of_sink;
            SmartDigraph::Node sink = SmartDigraph::nodeFromId(name_id_map["t" + to_string(rnd)]);
            SmartDigraph::Arc arc = g.addArc(source, sink);
            // Record arc ID given arc name in string
            name_id_map["s" + to_string(i) + "t" + to_string(rnd)] = g.id(arc);
            // Set capacity
            capacity_map[arc] = supply_map[source];
        }
    }
    // Check if every sink is connected to at least one source
    for (int i = 0; i < num_of_sink; i++) {
        SmartDigraph::Node sink = SmartDigraph::nodeFromId(name_id_map["t" + to_string(i)]);
        SmartDigraph::InArcIt a(g, sink); 
        if (a == INVALID) {
            cout << "Node t" << i << " is not connected;" << endl;
            // Randomly connect it to some source
            int rnd = rand() % num_of_source;
            SmartDigraph::Node source = SmartDigraph::nodeFromId(name_id_map["s" + to_string(rnd)]);
            SmartDigraph::Arc arc = g.addArc(source, sink);
            // Record arc ID given arc name in string
            name_id_map["s" + to_string(rnd) + "t" + to_string(i)] = g.id(arc);
            // Set capacity
            capacity_map[arc] = supply_map[source];
        }
    }
    // Add arcs between sinks and the global sink
    for (int i = 0; i < num_of_sink; i++) {
        int count = 0;
        SmartDigraph::Node sink = SmartDigraph::nodeFromId(name_id_map["t" + to_string(i)]);
        for (SmartDigraph::InArcIt a(g, sink); a!=INVALID; ++a) {
            count += supply_map[g.source(a)];
        }
        double weight = -prior_prob[i];
        for (int j = 1; j <= count; j++) {
            SmartDigraph::Arc arc = g.addArc(sink, gt);
            // Set capacity
            capacity_map[arc] = 1;
            // Set weight
            weight *= detect_prob[i];
            weight_map[arc] = weight;
        }
    }
}

/*
void run_network_simplex() {
    NetworkSimplex<SmartDigraph, int, double> ns(g);
    ns.resetParams();
    ns.upperMap(capacity_map).costMap(weight_map).supplyMap(supply_map).run();
}
*/

template<typename T> void print_queue(T& q) {
    while(!q.empty()) {
        std::cout << q.top().first << " ";
        q.pop();
    }
    std::cout << '\n';
}

unordered_set<string>
assign_extra_demand(int num_of_source, int num_of_sink, 
                    int sink_num, unordered_set<string> & elim_set, 
                    unsigned unused_supply[], vector<vector<unsigned>>& flow)
{
    // Initialization
    unordered_set<string> visited_set;  // Record names (string) of visited nodes
    queue<string> Q;                    // Use queue for Breadth-First Search
    Q.push("t" + to_string(sink_num));
    unordered_set<string> in_Q_set;     // Record nodes currently in Q for fast contains() check
    in_Q_set.insert("t" + to_string(sink_num));
    unordered_map<string, string> pred; // Record predecessors for building augmenting path
    for (int i = 0; i < num_of_source; i++) {
        pred["s" + to_string(i)] = "";
    }
    for (int i = 0; i < num_of_sink; i++) {
        pred["t" + to_string(i)] = "";
    }
    // Loop
    while (!Q.empty()) {
        string nd_name = Q.front(); Q.pop();
        in_Q_set.erase(nd_name);
        visited_set.insert(nd_name);
        SmartDigraph::Node nd = SmartDigraph::nodeFromId(name_id_map[nd_name]);
        // If the node is a sink
        if (nd_name.at(0) == 't') {
            for (SmartDigraph::InArcIt a(g, nd); a!=INVALID; ++a) {
                SmartDigraph::Node source = g.source(a);
                string source_name = node_name[source];
                // If cannot find source_name in Q, or visited_set, or elim_set
                if (in_Q_set.find(source_name) == in_Q_set.end() &&
                    visited_set.find(source_name) == visited_set.end() &&
                    elim_set.find(source_name) == elim_set.end())
                {
                    Q.push(source_name);
                    in_Q_set.insert(source_name);
                    pred[source_name] = nd_name;
                }
            }
        }
        // Else, the node is a source
        else {
            int nd_num = stoi(nd_name.substr(1));
            // If the source has no unused supply
            if (unused_supply[nd_num] == 0) {
                for (SmartDigraph::OutArcIt a(g, nd); a!=INVALID; ++a) {
                    SmartDigraph::Node sink = g.target(a);
                    string sink_name = node_name[sink];
                    int sink_num = stoi(sink_name.substr(1));
                    // If flow from nd_num (a source) to sink_num is positive,
                    // or cannot find source_name in Q, or visited_set, or elim_set
                    if (flow[nd_num][sink_num] > 0 &&
                        in_Q_set.find(sink_name) == in_Q_set.end() &&
                        visited_set.find(sink_name) == visited_set.end() &&
                        elim_set.find(sink_name) == elim_set.end())
                    {
                        Q.push(sink_name);
                        in_Q_set.insert(sink_name);
                        pred[sink_name] = nd_name;
                    }
                }
            }
            // Else, the source still has unused supply
            else {
                // Decrement unused_supply of the source by 1
                unused_supply[nd_num] -= 1;
                // Recursively build augmenting path
                auto cur = nd_name;
                while (1) {
                    string pre = pred[cur];
                    if (pre.empty())
                        break;
                    // For source
                    if (cur.at(0) == 's') {
                        flow[stoi(cur.substr(1))][stoi(pre.substr(1))]++;
                    }
                    // For sink
                    else {
                        flow[stoi(pre.substr(1))][stoi(cur.substr(1))]++;
                    }
                    cur = pre;
                }
                // There is no node to be eliminated! And remember to break the outer loop!
                visited_set.clear();
                break;
            }
        }
    }
    return visited_set;
}

double new_algo(int num_of_source, int num_of_sink, double arc_prob, 
              int supply_each, double prior_prob[], double detect_prob[])
{
    // Initialize the algorithm
    auto cmp = [](pair<double, int> p1, pair<double, int> p2) { return p1.first < p2.first; };
    priority_queue<pair<double, int>, vector<pair<double, int>>, decltype(cmp)> heap_of_weights(cmp);
    for (int i = 0; i < num_of_sink; i++) {
        pair<double, int> p = make_pair(prior_prob[i] * detect_prob[i], i);
        heap_of_weights.push(p);
    }
    unordered_set<string> elim_set;
    unsigned final_sink_demand[num_of_sink] = {};
    unsigned grand_total_supply = supply_each * num_of_source;
    unsigned unused_supply[num_of_source] = {};
    for (int i = 0; i < num_of_source; i++) {
        int nd_id = name_id_map["s" + to_string(i)];
        SmartDigraph::Node nd = SmartDigraph::nodeFromId(nd_id);
        unused_supply[i] = supply_map[nd];
    }
    vector<vector<unsigned>> flow(num_of_source, vector<unsigned>(num_of_sink, 0));
    // Main body of the algorithm
    while (grand_total_supply > 0) {
        auto top_element_heap = heap_of_weights.top(); heap_of_weights.pop();
        int sink_num = top_element_heap.second;
        string sink_name = "t" + to_string(sink_num);
        if (elim_set.find(sink_name) != elim_set.end()) {
            continue;
        }
        auto potential_elim_set = assign_extra_demand(num_of_source, num_of_sink,
                                                      sink_num, elim_set, 
                                                      unused_supply, flow);
        if (potential_elim_set.empty()) {
            grand_total_supply -= 1;
            final_sink_demand[sink_num] += 1;
            double old_weight = top_element_heap.first;
            double new_weight = old_weight * detect_prob[sink_num];
            heap_of_weights.push(make_pair(new_weight, sink_num));
        }
        else {
            elim_set.insert(potential_elim_set.begin(), potential_elim_set.end());
        }
    }
    
    // Output optimal value
    double opt_val = 0;
    for (int i = 0; i < num_of_sink; i++) {
        double temp = prior_prob[i];
        for (int j = 0; j < final_sink_demand[i]; j++) {
            temp *= detect_prob[i];
            opt_val += temp;
        }
    }
    return opt_val;
}


int main() {
    // Graph parameters
    const int num_of_source = 20;
    const int num_of_sink   = 60;
    const double arc_prob   = 0.7;
    const int supply_each   = 10;
    double prior_prob[num_of_sink];
    double detect_prob[num_of_sink];
    // Generate prior and detection probabilities for each sink
    std::mt19937 gen(10);
    std::uniform_real_distribution<> dis(0, 1);
    for (int i = 0; i < num_of_sink; i++) {
        prior_prob[i] = dis(gen);
        detect_prob[i] = dis(gen);
    }
    // Build the graph
    build_graph(num_of_source, num_of_sink, arc_prob, 
                supply_each, prior_prob, detect_prob);
    /*
    for(auto const &ent : name_id_map) {
        cout << ent.first << "," << ent.second << endl;
    }
    */
    // Run our new algorithm
    chrono::steady_clock::time_point start1 = chrono::steady_clock::now();
    double opt_val = new_algo(num_of_source, num_of_sink, arc_prob, 
                              supply_each, prior_prob, detect_prob);
    chrono::steady_clock::time_point end1 = chrono::steady_clock::now();
    cout << "New Algorithm time: "
         << chrono::duration_cast<chrono::milliseconds>(end1 - start1).count() << endl;
    cout << "New Algorithm result: " << opt_val << endl;
    
    // Run Lemon's Network Simplex algorithm
    NetworkSimplex<SmartDigraph, int, double> ns(g);
    ns.resetParams();
    ns.upperMap(capacity_map).costMap(weight_map).supplyMap(supply_map);
    chrono::steady_clock::time_point start2 = chrono::steady_clock::now();
    ns.run();
    chrono::steady_clock::time_point end2 = chrono::steady_clock::now();
    cout << "Network Simplex time: "
         << chrono::duration_cast<chrono::milliseconds>(end2 - start2).count() << endl;
    cout << "Network Simplex result: " << ns.totalCost<double>() << endl;
    

    /*
    int flow = 0;
    for(SmartDigraph::ArcIt a(g); a!=INVALID; ++a) {
        cout << "(" << capacity_map[a] << ","
             << ns.flow(a) << "), ";
        flow += ns.flow(a);
    }
    cout << flow << endl;
    */
    

    // Run Lemon's Cost Scaling algorithm
    CostScaling<SmartDigraph, int, double> cos(g);
    cos.resetParams();
    cos.upperMap(capacity_map).costMap(weight_map).supplyMap(supply_map);
    chrono::steady_clock::time_point start3 = chrono::steady_clock::now();
    cos.run();
    chrono::steady_clock::time_point end3 = chrono::steady_clock::now();
    cout << "Cost Scaling time: "
         << chrono::duration_cast<chrono::milliseconds>(end3 - start3).count() << endl;
    cout << "Cost Scaling result: " << cos.totalCost<double>() << endl;
    
    /*
    // Run Lemon's Capacity Scaling algorithm
    CapacityScaling<SmartDigraph, int, double> cas(g);
    cas.resetParams();
    cas.upperMap(capacity_map).costMap(weight_map).supplyMap(supply_map);
    clock_t start4 = clock();
    cas.run();
    clock_t end4 = clock();
    cout << "Capacity Scaling time: " << end4 - start4 << endl;
    cout << "Capacity Scaling result: " << cas.totalCost<double>() << endl;
    */
    
    /*
    // Run Lemon's Cycle Canceling algorithm
    CycleCanceling<SmartDigraph, int, double> cc(g);
    cc.resetParams();
    cc.upperMap(capacity_map).costMap(weight_map).supplyMap(supply_map);
    cc.run();
    cout << cc.totalCost<double>() << endl;
    */
}
