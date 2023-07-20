#include <fstream>
#include <iostream>
#include <vector>
#include <bits/stdc++.h>
using namespace std;

const uint16_t MAX_VERTICES = 10;
const uint32_t MAX_INSTRUCTIONS = 200;

#define set_bit(bitmask, idx) ( (bitmask) |= 1UL << (idx))
#define clear_bit(bitmask, idx) ( (bitmask) &= ~(1UL << (idx)))
#define get_bit(bitmask, idx) (((bitmask) >> (idx)) & 1U)

//Following decodes constraint.map uint32_t values. First 16 bits stores location(in bitmask), last 16 bits stores 0 or 1
#define constraint_val(val) ((uint16_t)((val)& 0xFFFFUL ))
#define constraint_loc(val) ((uint16_t) (( (val) >> 16) & 0xFFFFUL))


// This is for indexing into instr_constraint map(an array), a is source, b is target
#define key(a, b) ((a << 4) + b )

typedef unsigned __int128 uint128_t;
typedef struct shuffle_val {
    bool binary;
    uint16_t vector_width;
    uint16_t output[64]; // For each of the bytes in up to 512 bits, store byte num from input. Uses only the first 2^i for smaller vector width or larger packed values.

} shuffle_val;

typedef struct constraint {
    uint16_t source;
    uint16_t target;
    vector<uint32_t> map;
} constraint;

typedef struct instr {
    string name;
    uint16_t type; //0 = unary no mask, 1 = unary constant mask, 2 = unary register mask, 3 = binary no mask, 4 = binary constant mask, 5 = binary register mask
    uint16_t vector_width;
    uint16_t mask_position; //0,1,2

    uint32_t constraint_length;
    constraint* constraints;
    
} instr;

instr instr_list[MAX_INSTRUCTIONS];
//array<vector<unordered_set<uint16_t>>,MAX_INSTRUCTIONS> instr_valid_map;
array<vector<vector<uint16_t>>,MAX_INSTRUCTIONS> instr_valid_map;
//array<unordered_map<uint32_t,constraint*>,MAX_INSTRUCTIONS> instr_constraint_maps;
array<array<constraint*,512>,MAX_INSTRUCTIONS> instr_constraint_maps;
// array<unordered_map<pair<uint16_t,uint16_t>,constraint*, hash_pair>,MAX_INSTRUCTIONS> instr_constraint_maps;

int instr_binary_point=0;
int num_instructions =0;
vector<uint16_t> dag_order(0);

//Using immutable DAGs in adjacency list format as we simply take in input from pynauty 
class DAG{
public:
    uint16_t vertices;
    uint16_t distance;
    uint16_t difficulty;
    vector<vector<uint16_t>> edges; // Maps node to immediate successors
    vector<vector<uint16_t>> reverse_edges; // Maps nodes to immediately predecessors(must be length 1 or 2)
    vector<int> instructions; //This should hold list of indicies into instr_list for each vertex
    vector<array<uint16_t,128>> mask_values; //Current mask values, 2 means unset, 0,1 mean value set to 0,1
    //vector<vector<uint16_t>> intermediates; //Bit representation of intermediates. Each vertex stores mapping of each of 32 bytes from input to location in intermediate.
    
    vector<array<uint16_t,16>> candidate_locations; //For use in the dataflow v2 thing. 16 indices in array, counting by index in output vector!
    vector<array<uint16_t,16>> valid_preimage_1; //For each output location(length 16), set(or vector) of valid preimage locations.(single node for availability propogation) 
    vector<array<uint16_t,16>> valid_preimage_2; // Same as before, but 2nd predecessor node(in the event of binary)

    vector<vector<uint16_t>> update_order; //List of "downstream"(going up DAG) nodes in reverse order 
    
    vector<bool> inst_type;//true = unary, false = binary, vertices 0,1 defaulted to inputs(type doesn't matter/exist)
    vector<uint16_t> binary_order; //0 = order reverse_edges, 1 = reversed order of reverse_edges, 2 = unset
    vector<vector<bool>> downstream;//Calculated in same method as binary order. stores whether directly downstream of.
    vector<array<uint16_t,16>> path; //Chosen reverse_edge for each node in DAG ordered by output byte.

    vector<bool>reachable0; //reachable by 1st input
    vector<bool>reachable1; //reachable by 2nd input
    vector<uint16_t>distance0; //Distance to 1st input
    vector<uint16_t>distance1; //Distance to 2nd input
    DAG(uint16_t vertices_in){
        vertices = vertices_in;
        distance = 0;
        difficulty=0;
        edges =  vector<vector<uint16_t>>(vertices);
        reverse_edges =  vector<vector<uint16_t>>(vertices);
        inst_type = vector<bool>(vertices);
        instructions = vector<int>(vertices);
        mask_values = vector<array<uint16_t,128>>(vertices);
        //intermediates = vector<vector<uint16_t>>(vertices);
        candidate_locations = vector<array<uint16_t,16>>(vertices);
        valid_preimage_1 = vector<array<uint16_t,16>>(vertices);
        valid_preimage_2 = vector<array<uint16_t,16>>(vertices);
        update_order = vector<vector<uint16_t>>(vertices);
        binary_order = vector<uint16_t>(vertices);
        downstream = vector<vector<bool>>(vertices);
        reachable0 = vector<bool>(vertices);
        reachable1 = vector<bool>(vertices);
        distance0 = vector<uint16_t>(vertices);
        distance1 = vector<uint16_t>(vertices);
        path = vector<array<uint16_t,16>>(vertices);
        for(int i =0; i < vertices; i++){
            mask_values[i] = array<uint16_t,128>();
            instructions[i] = 0xFFFF;
            binary_order[i] = 2;
            reachable0[i] = false;
            reachable1[i] = false;
            distance0[i] = 0xFFFF;
            distance1[i] = 0xFFFF;
            //intermediates[i] = vector<uint16_t>(32);
            update_order[i] = vector<uint16_t>(0);
            for(int j = 0;j<32;j++){
                //intermediates[i][j]=16;
            }
            for(int j =0;j<128;j++){
                mask_values[i][j]=2;
            }
            for(int j =0; j < 16; j++){
                candidate_locations[i][j] = 0xFFFF;
                valid_preimage_1[i][j] = 0xFFFF;
                valid_preimage_2[i][j] = 0xFFFF;
                path[i][j] = 0xFFFF;
            }
            
        }
        for(int j = 0;j < 16; j++){
            candidate_locations[vertices-1][j] = 1 <<j;
        }
        

    }
    void recalculate_preimage(vector<uint16_t*> &undo_locations, vector<uint16_t> &undo_values,int vertex){
        //assert(vertex!=0 && vertex!=1);
        uint16_t inst = instructions[vertex];
        if(inst_type[vertex]){//Unary
            if(inst!=0xFFFF){ //Instruction is set
                if(instr_list[inst].type==0 ){ //Non Mask instruction
                    for(uint16_t target = 0; target < 16; target++){
                        uint16_t temp_val = 0;
                        //valid_preimage_1[vertex][target] = 0;
                        for(auto source: instr_valid_map[inst][target]){
                            set_bit(temp_val, source);
                        }
                        if(temp_val!=valid_preimage_1[vertex][target]){
                            undo_locations.push_back(&valid_preimage_1[vertex][target]);
                            undo_values.push_back(valid_preimage_1[vertex][target]);
                            valid_preimage_1[vertex][target] = temp_val;
                        }
                    }
                }else{ //Masked unary instruction
                    for(uint16_t target = 0; target < 16; target++){
                        //valid_preimage_1[vertex][target] = 0;
                        uint16_t temp_val = 0;
                        for(auto source : instr_valid_map[inst][target]){
                            constraint* temp = instr_constraint_maps[inst][key(source,target)];
                            bool valid = true;
                            for(auto val: temp->map){
                                uint16_t loc = constraint_loc(val);
                                uint16_t set_value = constraint_val(val);
                                
                                uint16_t current_value = mask_values[vertex][loc];
                                if(current_value !=2 && current_value!=set_value){
                                    //conflict
                                    valid = false;
                                    break;
                                }
                            }
                            if(valid){
                                set_bit(temp_val,source);
                            }
                        }
                        if(temp_val != valid_preimage_1[vertex][target]){
                            undo_locations.push_back(&valid_preimage_1[vertex][target]);
                            undo_values.push_back(valid_preimage_1[vertex][target]);
                            valid_preimage_1[vertex][target] = temp_val;
                        }
                    }
                }
            }//If instruction no set, no need to update
        }else{ //Binary
            if(instructions[vertex]!=0xFFFF){
                if(instr_list[inst].type==3){ //Non-masked instruction
                    for(uint16_t target = 0; target < 16; target++){
                        // undo_locations.push_back(&valid_preimage_1[vertex][target]);
                        // undo_values.push_back(valid_preimage_1[vertex][target]);
                        
                        // undo_locations.push_back(&valid_preimage_2[vertex][target]);
                        // undo_values.push_back(valid_preimage_2[vertex][target]);
                        uint16_t temp_val_1 = 0;
                        uint16_t temp_val_2 = 0;
                        // valid_preimage_1[vertex][target] = 0;
                        // valid_preimage_2[vertex][target] = 0;
                        for(auto source: instr_valid_map[inst][target]){
                            if(source<16){
                                set_bit(temp_val_1,source);
                            }
                            else{
                                set_bit(temp_val_2,source%16);
                            }
                        }
                        if(temp_val_1 != valid_preimage_1[vertex][target]){
                            undo_locations.push_back(&valid_preimage_1[vertex][target]);
                            undo_values.push_back(valid_preimage_1[vertex][target]);
                            valid_preimage_1[vertex][target] = temp_val_1;
                        }
                        if(temp_val_2 != valid_preimage_2[vertex][target]){
                            undo_locations.push_back(&valid_preimage_2[vertex][target]);
                            undo_values.push_back(valid_preimage_2[vertex][target]);
                            valid_preimage_2[vertex][target] = temp_val_2;
                        }
                    }
                }else{ //Masked instruction
                    for(uint16_t target = 0; target < 16; target++){
                        // undo_locations.push_back(&valid_preimage_1[vertex][target]);
                        // undo_values.push_back(valid_preimage_1[vertex][target]);
                        
                        // undo_locations.push_back(&valid_preimage_2[vertex][target]);
                        // undo_values.push_back(valid_preimage_2[vertex][target]);

                        uint16_t temp_val_1 = 0;
                        uint16_t temp_val_2 = 0;
                        // valid_preimage_1[vertex][target] = 0;
                        // valid_preimage_2[vertex][target] = 0;

                        for(auto source : instr_valid_map[inst][target]){
                            constraint* temp = instr_constraint_maps[inst][key(source,target)];

                            bool valid = true;

                            for(auto val: temp->map){
                                uint16_t loc = constraint_loc(val);
                                uint16_t set_value = constraint_val(val);
                                
                                uint16_t current_value = mask_values[vertex][loc];
                                if(current_value !=2 && current_value!=set_value){
                                    //conflict
                                    valid = false;
                                    break;
                                }
                            }
                            if(valid){
                                if(source<16){
                                    set_bit(temp_val_1,source);
                                }
                                else{
                                    set_bit(temp_val_2,source%16);
                                }
                            }
                        }
                        if(temp_val_1 != valid_preimage_1[vertex][target]){
                            undo_locations.push_back(&valid_preimage_1[vertex][target]);
                            undo_values.push_back(valid_preimage_1[vertex][target]);
                            valid_preimage_1[vertex][target] = temp_val_1;
                        }
                        if(temp_val_2 != valid_preimage_2[vertex][target]){
                            undo_locations.push_back(&valid_preimage_2[vertex][target]);
                            undo_values.push_back(valid_preimage_2[vertex][target]);
                            valid_preimage_2[vertex][target] = temp_val_2;
                        }
                    }
                }
            }
        }
        // cout << "PreImages:\n";
        // for(int i =0;i<16;i++){
        //     bitset<16> temp(valid_preimage_1[vertex][i]);
        //     bitset<16> temp2(valid_preimage_2[vertex][i]);
        //     cout << temp << "," << temp2 << "\n";
        // }
    }
    void update_candidate_locations_good(vector<uint16_t*> &undo_locations, 
                                    vector<uint16_t> &undo_values,
                                    uint16_t vertex,
                                    vector<uint16_t> &byte_order,
                                    uint16_t byte_index,
                                    uint16_t next_vertex,
                                    uint16_t next_loc){
    candidate_locations[next_vertex][byte_order[byte_index]] = 1 << next_loc;
    //cout << "SET "<< next_vertex << "," << byte_order[byte_index] << " TO 1<<" <<next_loc << "\n" << flush; 
    for(uint16_t cur_vertex : update_order[next_vertex]){
        uint16_t inst = instructions[vertex];

        uint16_t i = byte_order[byte_index];

        undo_locations.push_back(&candidate_locations[cur_vertex][i]);
        undo_values.push_back(candidate_locations[cur_vertex][i]);

        candidate_locations[cur_vertex][i] = 0;
        for(auto successor : edges[cur_vertex]){
            if(!downstream[next_vertex][successor])
                continue;
            uint16_t successor_locs = candidate_locations[successor][i];
            uint16_t total_candidates = __builtin_popcount(successor_locs);
            if(inst_type[successor]){//unary
                for(uint16_t j =0 ; j < total_candidates; j++){
                    uint16_t next_loc = __builtin_ctz(successor_locs);
                    candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                    clear_bit(successor_locs,next_loc);
                }
            }else{//binary
                if(binary_order[successor]==2){
                    for(uint16_t j = 0; j < total_candidates; j ++){
                        uint16_t next_loc = __builtin_ctz(successor_locs);
                        candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                        candidate_locations[cur_vertex][i] |= valid_preimage_2[successor][next_loc];
                        clear_bit(successor_locs,next_loc);
                    }
                }else if(binary_order[successor]==0 && cur_vertex== reverse_edges[successor][0]||
                    binary_order[successor]==1 && cur_vertex == reverse_edges[successor][1]){
                    for(uint16_t j = 0; j < total_candidates; j ++){
                        uint16_t next_loc = __builtin_ctz(successor_locs);
                        candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                        clear_bit(successor_locs,next_loc);
                    }
                }else{
                    for(uint16_t j = 0; j < total_candidates; j ++){
                        uint16_t next_loc = __builtin_ctz(successor_locs);
                        candidate_locations[cur_vertex][i] |= valid_preimage_2[successor][next_loc];
                        clear_bit(successor_locs,next_loc);
                    }
                }

            }
        }
    }
    for(uint16_t cur_vertex : update_order[vertex]){//over vertices
        //cout <<"Updating Vertex:" <<  cur_vertex << "\n";
        uint16_t inst = instructions[vertex];
        for(uint16_t temp = byte_index+1; temp < byte_order.size(); temp++){
            uint16_t i = byte_order[temp];

            undo_locations.push_back(&candidate_locations[cur_vertex][i]);
            undo_values.push_back(candidate_locations[cur_vertex][i]);

            candidate_locations[cur_vertex][i] = 0;
            for(auto successor : edges[cur_vertex]){
                uint16_t successor_locs = candidate_locations[successor][i];
                uint16_t total_candidates = __builtin_popcount(successor_locs);
                if(inst_type[successor]){//unary
                    for(uint16_t j =0 ; j < total_candidates; j++){
                        uint16_t next_loc = __builtin_ctz(successor_locs);
                        candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                        clear_bit(successor_locs,next_loc);
                    }
                }else{//binary
                    if(binary_order[successor]==2){
                        for(uint16_t j = 0; j < total_candidates; j ++){
                            uint16_t next_loc = __builtin_ctz(successor_locs);
                            candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                            candidate_locations[cur_vertex][i] |= valid_preimage_2[successor][next_loc];
                            clear_bit(successor_locs,next_loc);
                        }
                    }else if(binary_order[successor]==0 && cur_vertex== reverse_edges[successor][0]||
                        binary_order[successor]==1 && cur_vertex == reverse_edges[successor][1]){
                        for(uint16_t j = 0; j < total_candidates; j ++){
                            uint16_t next_loc = __builtin_ctz(successor_locs);
                            candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                            clear_bit(successor_locs,next_loc);
                        }
                    }else{
                        for(uint16_t j = 0; j < total_candidates; j ++){
                            uint16_t next_loc = __builtin_ctz(successor_locs);
                            candidate_locations[cur_vertex][i] |= valid_preimage_2[successor][next_loc];
                            clear_bit(successor_locs,next_loc);
                        }
                    }

                }
            }
        }
    }
}

void update_candidate_locations(vector<uint16_t*> &undo_locations, 
                                    vector<uint16_t> &undo_values,
                                    uint16_t vertex,
                                    vector<uint16_t> &byte_order,
                                    uint16_t byte_index){
        for(uint16_t cur_vertex : update_order[vertex]){//over vertices
            //cout <<"Updating Vertex:" <<  cur_vertex << "\n";
            uint16_t inst = instructions[vertex];
            for(uint16_t temp = byte_index; temp < byte_order.size(); temp++){
                uint16_t i = byte_order[temp];
                undo_locations.push_back(&candidate_locations[cur_vertex][i]);
                undo_values.push_back(candidate_locations[cur_vertex][i]);

                candidate_locations[cur_vertex][i] = 0;
                for(auto successor : edges[cur_vertex]){
                    uint16_t successor_locs = candidate_locations[successor][i];
                    uint16_t total_candidates = __builtin_popcount(successor_locs);
                    if(inst_type[successor]){//unary
                        for(uint16_t j =0 ; j < total_candidates; j++){
                            uint16_t next_loc = __builtin_ctz(successor_locs);
                            candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                            clear_bit(successor_locs,next_loc);
                        }
                    }else{//binary
                        if(binary_order[successor]==2){
                            for(uint16_t j = 0; j < total_candidates; j ++){
                                uint16_t next_loc = __builtin_ctz(successor_locs);
                                candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                                candidate_locations[cur_vertex][i] |= valid_preimage_2[successor][next_loc];
                                clear_bit(successor_locs,next_loc);
                            }
                        }else if(binary_order[successor]==0 && cur_vertex== reverse_edges[successor][0]||
                            binary_order[successor]==1 && cur_vertex == reverse_edges[successor][1]){
                            for(uint16_t j = 0; j < total_candidates; j ++){
                                uint16_t next_loc = __builtin_ctz(successor_locs);
                                candidate_locations[cur_vertex][i] |= valid_preimage_1[successor][next_loc];
                                clear_bit(successor_locs,next_loc);
                            }
                        }else{
                            for(uint16_t j = 0; j < total_candidates; j ++){
                                uint16_t next_loc = __builtin_ctz(successor_locs);
                                candidate_locations[cur_vertex][i] |= valid_preimage_2[successor][next_loc];
                                clear_bit(successor_locs,next_loc);
                            }
                        }

                    }
                }
            }
        }
    }
    bool check_valid(vector<uint16_t*> &undo_locations, vector<uint16_t> &undo_values,shuffle_val &desired, uint16_t cur_vertex,uint16_t cur_byte){
        bool valid = true;
        for(uint16_t i=0; i < 16; i++){
            // bitset<16> temp(candidate_locations[0][i]);
            // bitset<16> temp2(candidate_locations[1][i]);
            // cout << i << "," << temp << "," << temp2 << "\n";
            uint16_t input_loc = desired.output[i];
            if(input_loc < 16){
                if(get_bit(candidate_locations[0][i],input_loc) !=1){
                    valid = false;
                    break;
                }
            }else{
                if(get_bit(candidate_locations[1][i],input_loc-16) !=1){
                    valid = false;
                    break;
                }
            }
        }
        if(valid){
            uint16_t input_loc = desired.output[cur_byte];
            if(cur_vertex !=0 && cur_vertex !=1){
                if(input_loc < 16){
                    if(!downstream[cur_vertex][0]){
                        return false;
                    }
                }else{
                    if(!downstream[cur_vertex][1]){
                        return false;
                    }
                }
            }else if(cur_vertex==0){
                if(input_loc >=16)
                    return false;
            }else if(cur_vertex==1){
                if(input_loc<16)
                    return false;
            }
            return true;
        }
        return false;
    }




    void calculate_reverse_edges(){
        for(int i =0; i < vertices; i++){
            reverse_edges[i] = vector<uint16_t>();
            reverse_edges[i].reserve(2);
        }

        for(uint16_t i =0; i < vertices; i++){
            for(uint16_t temp: edges[i]){
                reverse_edges[temp].push_back(i);
            }
        }


    }
    void print_state(){
        for(int i =2; i < vertices;i++){
            if(instructions[i]<num_instructions)
                cout << "VERTEX NUMBER: " << i <<"," << instr_list[instructions[i]].name << ",";
            else if(instructions[i]==0xFFFF)
                cout << "VERTEX NUMBER: " << i << "," << "UNNEEDED"; 
            else
                cout << "VERTEX NUMBER: " << i << "," << "ERROR" << instructions[i] << ","; 
            cout << "\nEdges:";
            for(int j =0; j < reverse_edges[i].size();j++){
                cout << reverse_edges[i][j] << ",";
            }
            // for(auto elem : mask_values[i]){
            //     cout << elem.first << ":" << elem.second << "\n";
            // }
            cout << "\n";
            for(int j =0;j<128;j++){
                if(mask_values[i][j]!=2){
                    cout << j << ":" << mask_values[i][j] << "\n";
                }
            }
            cout << "\n";
        }
    }
    void calculate_inst_types(){
        for(int i =0; i < vertices; i++){
            inst_type[i] = false;
        }
        for(int i =0; i < vertices; i++){
            for(uint16_t temp : edges[i]){
                inst_type[temp] = !inst_type[temp]; //If each instruction either unary or binary, just flip each time we see a use
            }
        }
    }
    void calculate_difficulty(){
        uint16_t unary_counter=0;
        uint16_t binary_counter=0;
        for(int i =2; i < vertices; i++){
            if(inst_type[i])
                unary_counter++;
            else
                binary_counter++;
        }
        difficulty = unary_counter*2 + binary_counter;
        // vector<bool> visited(vertices,false);
        // queue<pair<uint16_t,uint16_t>> bfs;
        // visited[vertices-1]=true;
        // bfs.push(pair<uint16_t,uint16_t>{vertices-1,0});
        // while(!bfs.empty()){
        //     auto current = bfs.front();
        //     bfs.pop();
        //     if(current.first ==0 || current.first==1 || !inst_type[current.first]){
        //         difficulty = (distance) * (100) + vertices*10+ current.second;
        //         break;
        //     }
        //     for(uint16_t temp: reverse_edges[current.first]){
        //         if(visited[temp])
        //             continue;
        //         else{
        //             visited[temp]=true;
        //             bfs.push(pair<uint16_t,uint16_t>{temp, current.second+1});
        //         }
        //     }
        // }
    }
    void calculate_update_order(){
        for(uint16_t i =2; i < vertices; i ++){
            //vector<bool> visited(vertices,false);
            downstream[i] = vector<bool>(vertices,false);
            queue<uint16_t> bfs;
            bfs.push(i);
            downstream[i][i] = true;
            while(!bfs.empty()){
                auto current = bfs.front();
                bfs.pop();
                //cout << current <<"," << &reverse_edges<< "\n" << flush;
                for(uint16_t temp: reverse_edges[current]){
                    //cout << "PREVIOUS:" << temp <<"\n" << flush;
                    if(downstream[i][temp])
                        continue;
                    downstream[i][temp] = true;
                    if(temp ==0 || temp==1)
                        continue;
                    bfs.push(temp);
                }
            }
            for(int j = i-1; j >= 0; j--){
                if(downstream[i][j])
                    update_order[i].push_back(j);
            }


        }
    }
    void calculate_reachable(){
        reachable0[0] = true;
        reachable1[1] = true;
        distance0[0] = 0;
        distance1[1] = 0;

        vector<bool> visited(vertices,false);
        visited[0] = true;
        queue<pair<uint16_t,uint16_t>> bfs;
        bfs.push(pair<uint16_t,uint16_t>{0,0});
        while(!bfs.empty()){
            auto current = bfs.front();
            bfs.pop();
            if(current.first == vertices-1){
                distance = current.second;
            }
            distance0[current.first] = current.second;
            for(uint16_t temp: edges[current.first]){
                if(visited[temp])
                    continue;
                else{
                    visited[temp] = true;
                    reachable0[temp] = true;
                    bfs.push(pair<uint16_t,uint16_t>{temp,current.second+1});
                }
            }
        }

        fill(visited.begin(),visited.end(),false);
        visited[1] = true;
        bfs.push(pair<uint16_t,uint16_t>{1,0});
        while(!bfs.empty()){
            auto current = bfs.front();
            bfs.pop();
            if(current.first == vertices-1){
                if(current.second<distance)
                    distance = current.second;
            }
            distance1[current.first] = current.second;
            for(uint16_t temp: edges[current.first]){
                if(visited[temp])
                    continue;
                else{
                    visited[temp] = true;
                    reachable1[temp] = true;
                    bfs.push(pair<uint16_t,uint16_t>{temp,current.second+1});
                }
            }
        }
    }
    ~DAG() {

    }
};
vector<DAG> dags;
uint32_t dag_vertices_to_index[MAX_VERTICES+1];
void read_dags(uint16_t max_depth){
    ifstream read_file("dag_data.txt");
    uint32_t num_dags;
    read_file >> num_dags;

    dags.reserve(num_dags);
    uint16_t current_vertex = 0;
    vector<pair<int,uint16_t>> temp_order(0);
    temp_order.reserve(num_dags);
    for(int i =0; i < num_dags; i++){ //iterating over number of dags
        uint16_t vtx;
        read_file >> vtx;
        if(vtx != current_vertex){
            dag_vertices_to_index[vtx] = i;
            current_vertex = vtx;
        }
        dags.push_back(DAG(vtx));


        uint32_t num_outgoing;
        int counter;
        for(int j =0; j < vtx-1; j++){ //iterating over vertices of dag
            read_file >> num_outgoing; //Represents number of edges outgoing from vertex j
            dags[i].edges[j] = vector<uint16_t>();
            dags[i].edges[j].reserve(num_outgoing);
            for(int idx =0; idx < num_outgoing; idx++){ //iterating over edges of adjlist per vertex
                uint16_t temp;
                read_file >> temp;
                dags[i].edges[j].push_back(temp);
                //cout << temp;
            }
        }
        dags[i].edges[vtx-1] = vector<uint16_t>(0);
        dags[i].calculate_inst_types();
        dags[i].calculate_reverse_edges();
        dags[i].calculate_reachable();
        dags[i].calculate_difficulty();
        dags[i].calculate_update_order();
        if(dags[i].vertices<=max_depth+2)
            temp_order.push_back(pair<int,uint16_t>{i, dags[i].difficulty});
        
    } 
    sort(temp_order.begin(), temp_order.end(), [](auto &left, auto &right) {
    return left.second < right.second;
});
    dag_order.reserve(num_dags);
    for(int i =0;i<temp_order.size();i++){
        dag_order.push_back(temp_order[i].first);
    }
    


}
uint64_t timeSinceEpochMillisec() {
  using namespace std::chrono;
  return duration_cast<milliseconds>(system_clock::now().time_since_epoch()).count();
}
void read_constraints(){
    ifstream read_file("constraint_data4.txt");
    uint32_t num_insts;
    read_file >> num_insts;

    num_instructions = num_insts;

    for(int i =0; i < num_insts;i++){
        instr_valid_map[i] = vector<vector<uint16_t>>(16);
        instr_constraint_maps[i] = array<constraint*,512>();
        for(int j =0;j<16;j++){
            instr_valid_map[i][j]=vector<uint16_t>(0);
            instr_valid_map[i][j].reserve(16);
        }
    }
    for(int i = 0; i < num_insts; i++){
        string name;
        uint16_t type;
        uint16_t vector_width;
        uint16_t mask_position;
        uint32_t constraint_length;

        read_file >> name >> type >> vector_width >> mask_position >> constraint_length;
        instr_list[i] = {name, type, vector_width, mask_position, constraint_length, new constraint[constraint_length]};

        if(type==3 && instr_binary_point==0){
            instr_binary_point = i;
        }
        

        for(int j =0; j < constraint_length; j++){
            uint16_t source;
            uint16_t target;
            uint32_t num_constraints;

            read_file >> source >> target >> num_constraints;
            instr_valid_map[i][target].push_back(source);
            
            // if(name=="_mm_cvtepi8_epi64"){
            //     cout << "INFO:" << source << "," << target << "\n";
            // }
            //unordered_map<uint16_t,uint16_t> umap;
            vector<uint32_t> umap;
            umap.reserve(num_constraints);
            for(int k =0; k < num_constraints; k++){
                uint16_t location;
                uint16_t bit_val;
                read_file >> location >> bit_val;
                //umap[location] = bit_val;
                umap.push_back((uint32_t)location <<16 | bit_val);
            }
 
            constraint* temp = new constraint{source, target, umap};
            instr_constraint_maps[i][key(source,target)] = temp;
            //instr_list[i].constraints[j] = *temp;
        }
        for(int j=0;j<16;j++){
            sort(instr_valid_map[i][j].begin(),instr_valid_map[i][j].end());
        }


    }



}
bool backtracking_recursive(shuffle_val &desired,
                            vector<uint16_t> &byte_order,
                            uint16_t byte_index,
                            uint16_t cur_vertex,
                            uint16_t depth,
                            DAG &dag 
);
bool unary_nomask_new(shuffle_val &desired,
                    vector<uint16_t> &byte_order,
                    uint16_t byte_index,
                    uint16_t depth,
                    DAG &dag,
                    uint16_t cur_vertex,
                    uint16_t cur_byte){
    vector<uint16_t*> undo_locations;
    vector<uint16_t> undo_values;
    //assert(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte])==1);
    uint16_t cur_loc = __builtin_ctz(dag.candidate_locations[cur_vertex][cur_byte]);
    uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
    dag.recalculate_preimage(undo_locations,undo_values,cur_vertex);
    if(__builtin_popcount(dag.valid_preimage_1[cur_vertex][cur_loc])<1){
        return false;
    }
    //assert(__builtin_popcount(dag.valid_preimage_1[cur_vertex][cur_loc])==1);
    uint16_t prev_loc = __builtin_ctz(dag.valid_preimage_1[cur_vertex][cur_loc]);
    dag.update_candidate_locations_good(undo_locations,undo_values,cur_vertex, byte_order, byte_index,vertex_1, prev_loc);
    if(dag.check_valid(undo_locations,undo_values,desired,vertex_1, cur_byte)){
        if(backtracking_recursive(desired, byte_order, byte_index, vertex_1, depth+1,dag)){
            return true;
        }
    }
    for(int i = 0; i < undo_locations.size(); i++){
        *undo_locations[i] = undo_values[i];
    }
    return false;

}

bool unary_mask_new(shuffle_val &desired,
                    vector<uint16_t> &byte_order,
                    uint16_t byte_index,
                    uint16_t depth,
                    DAG &dag,
                    uint16_t cur_vertex,
                    uint16_t cur_byte){
    uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
    if(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte])<1)
        return false;
    if(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte])!=1){
        throw invalid_argument("ERROR");
    }
    //assert(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte])==1);
    uint16_t cur_loc = __builtin_ctz(dag.candidate_locations[cur_vertex][cur_byte]);

    uint16_t candidate_pre_locs  = dag.valid_preimage_1[cur_vertex][cur_loc];

    uint16_t total_options = __builtin_popcount(candidate_pre_locs);
    for(uint16_t opts = 0; opts < total_options; opts++){
        uint16_t source_opt = __builtin_ctz(candidate_pre_locs);
        constraint* temp = instr_constraint_maps[dag.instructions[cur_vertex]][key(source_opt, cur_loc)];
        vector<uint16_t*> undo_locations;
        vector<uint16_t> undo_values;

        for(auto val : temp->map){
            uint16_t loc = constraint_loc(val);
            uint16_t set_val = constraint_val(val);
            uint16_t current_value = dag.mask_values[cur_vertex][loc];

            if(set_val != current_value){
                undo_locations.push_back(&dag.mask_values[cur_vertex][loc]);
                undo_values.push_back(dag.mask_values[cur_vertex][loc]);

                dag.mask_values[cur_vertex][loc] = set_val;
            }
        }
        dag.recalculate_preimage(undo_locations,undo_values,cur_vertex);
        dag.update_candidate_locations_good(undo_locations,undo_values,cur_vertex, byte_order, byte_index,vertex_1,source_opt);
        if(dag.check_valid(undo_locations,undo_values,desired, vertex_1, cur_byte)){
            if(backtracking_recursive(desired, byte_order, byte_index, vertex_1, depth+1,dag)){
                return true;
            }
        }
        for(int i = 0; i < undo_locations.size(); i++){
            *undo_locations[i] = undo_values[i];
        }
        
        clear_bit(candidate_pre_locs,source_opt);
    }
    return false;
}
bool binary_nomask_new(shuffle_val &desired,
                    vector<uint16_t> &byte_order,
                    uint16_t byte_index,
                    uint16_t depth,
                    DAG &dag,
                    uint16_t cur_vertex,
                    uint16_t cur_byte){
    for(uint16_t binary_ordering = 0; binary_ordering < 2; binary_ordering++){
        dag.binary_order[cur_vertex] = binary_ordering;
        vector<uint16_t*> undo_locations;
        vector<uint16_t> undo_values;
        //assert(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte])==1);
        uint16_t cur_loc = __builtin_ctz(dag.candidate_locations[cur_vertex][cur_byte]);
        uint16_t vertex_1;
        uint16_t vertex_2;
        if(dag.binary_order[cur_vertex]==0){
            vertex_1 = dag.reverse_edges[cur_vertex][0];
            vertex_2 = dag.reverse_edges[cur_vertex][1];
        }else if(dag.binary_order[cur_vertex]==1){
            vertex_1 = dag.reverse_edges[cur_vertex][1];
            vertex_2 = dag.reverse_edges[cur_vertex][0];
        }else{
            __builtin_unreachable();
        }
        uint16_t next_vertex;
        dag.recalculate_preimage(undo_locations,undo_values,cur_vertex);
        if(__builtin_popcount(dag.valid_preimage_1[cur_vertex][cur_loc]==0)){
            //assert(__builtin_popcount(dag.valid_preimage_2[cur_vertex][cur_loc])==1); //vertex 2
            uint16_t prev_loc = __builtin_ctz(dag.valid_preimage_2[cur_vertex][cur_loc]);
            next_vertex = vertex_2;
            dag.update_candidate_locations_good(undo_locations,undo_values,cur_vertex, byte_order, byte_index, vertex_2, prev_loc);
       
        }else{
            //assert(__builtin_popcount(dag.valid_preimage_1[cur_vertex][cur_loc])==1); //vertex 1
            uint16_t prev_loc = __builtin_ctz(dag.valid_preimage_1[cur_vertex][cur_loc]);
            next_vertex = vertex_1;
            dag.update_candidate_locations_good(undo_locations,undo_values,cur_vertex, byte_order, byte_index, vertex_1, prev_loc);
       
        }
    

        if(dag.check_valid(undo_locations,undo_values,desired, next_vertex, cur_byte)){
            // uint16_t vertex_1;
            // uint16_t vertex_2;
            // if(dag.binary_order[cur_vertex]==0){
            //     vertex_1 = dag.reverse_edges[cur_vertex][0];
            //     vertex_2 = dag.reverse_edges[cur_vertex][1];
            // }else if(dag.binary_order[cur_vertex]==1){
            //     vertex_1 = dag.reverse_edges[cur_vertex][1];
            //     vertex_2 = dag.reverse_edges[cur_vertex][0];
            // }else{
            //     __builtin_unreachable();
            // }

            if(next_vertex==vertex_2){
                undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
                undo_values.push_back(dag.path[cur_vertex][cur_byte]);
                dag.path[cur_vertex][cur_byte] = vertex_2;
                if(backtracking_recursive(desired, byte_order, byte_index, vertex_2, depth+1, dag))
                    return true;
            }else{
                undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
                undo_values.push_back(dag.path[cur_vertex][cur_byte]);
                dag.path[cur_vertex][cur_byte] = vertex_1;
                if(backtracking_recursive(desired, byte_order, byte_index, vertex_1, depth+1, dag))
                    return true;
            }
        }
        for(int i = 0; i < undo_locations.size(); i++){
            *undo_locations[i] = undo_values[i];
        }
    }
    dag.binary_order[cur_vertex]=2;
    return false;
}


bool binary_mask_new(shuffle_val &desired,
                    vector<uint16_t> &byte_order,
                    uint16_t byte_index,
                    uint16_t depth,
                    DAG &dag,
                    uint16_t cur_vertex,
                    uint16_t cur_byte){
    uint16_t vertex_1;
    uint16_t vertex_2;
    if(dag.binary_order[cur_vertex]==0){
        vertex_1 = dag.reverse_edges[cur_vertex][0];
        vertex_2 = dag.reverse_edges[cur_vertex][1];
    }else if(dag.binary_order[cur_vertex]==1){
        vertex_1 = dag.reverse_edges[cur_vertex][1];
        vertex_2 = dag.reverse_edges[cur_vertex][0];
    }else{
        __builtin_unreachable();
    }
    if(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte])!=1){
        bitset<16> temp(dag.candidate_locations[cur_vertex][cur_byte]);
        cout << temp << "\n" << flush;
        throw invalid_argument("Probably unreachable");
    }
    //assert(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte])==1);
    uint16_t cur_loc = __builtin_ctz(dag.candidate_locations[cur_vertex][cur_byte]);

    //2 cases of iterate over vertex 1 or 2 of binary inputs
    //case 1
    uint16_t candidate_pre_locs  = dag.valid_preimage_1[cur_vertex][cur_loc];
    //cout << "PREIMAGES INFO:" << candidate_pre_locs << "\n";
    uint16_t total_options = __builtin_popcount(candidate_pre_locs);
    for(uint16_t opts = 0; opts < total_options; opts++){
        uint16_t source_opt = __builtin_ctz(candidate_pre_locs);
        constraint* temp = instr_constraint_maps[dag.instructions[cur_vertex]][key(source_opt, cur_loc)];
        //cout << source_opt << "," << cur_loc << "," << key(source_opt,cur_loc) << "\n" << flush;
        vector<uint16_t*> undo_locations;
        vector<uint16_t> undo_values;

        for(auto val : temp->map){
            uint16_t loc = constraint_loc(val);
            uint16_t set_val = constraint_val(val);
            uint16_t current_value = dag.mask_values[cur_vertex][loc];

            if(set_val != current_value){
                undo_locations.push_back(&dag.mask_values[cur_vertex][loc]);
                undo_values.push_back(dag.mask_values[cur_vertex][loc]);

                dag.mask_values[cur_vertex][loc] = set_val;
            }
        }
        undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
        undo_values.push_back(dag.path[cur_vertex][cur_byte]);
        dag.path[cur_vertex][cur_byte] = vertex_1;
        dag.recalculate_preimage(undo_locations,undo_values,cur_vertex);
        dag.update_candidate_locations_good(undo_locations,undo_values,cur_vertex, byte_order, byte_index, vertex_1, source_opt);
        if(dag.check_valid(undo_locations,undo_values,desired, vertex_1, cur_byte)){
            if(backtracking_recursive(desired, byte_order, byte_index, vertex_1, depth+1,dag)){
                return true;
            }
        }
        for(int i = 0; i < undo_locations.size(); i++){
            *undo_locations[i] = undo_values[i];
        }
        
        clear_bit(candidate_pre_locs,source_opt);
    }
    //case 2
    candidate_pre_locs  = dag.valid_preimage_2[cur_vertex][cur_loc];
    total_options = __builtin_popcount(candidate_pre_locs);
    for(uint16_t opts = 0; opts < total_options; opts++){
        uint16_t source_opt = __builtin_ctz(candidate_pre_locs);
        constraint* temp = instr_constraint_maps[dag.instructions[cur_vertex]][key(source_opt+16, cur_loc)];
        vector<uint16_t*> undo_locations;
        vector<uint16_t> undo_values;

        for(auto val : temp->map){
            uint16_t loc = constraint_loc(val);
            uint16_t set_val = constraint_val(val);
            uint16_t current_value = dag.mask_values[cur_vertex][loc];

            if(set_val != current_value){
                undo_locations.push_back(&dag.mask_values[cur_vertex][loc]);
                undo_values.push_back(dag.mask_values[cur_vertex][loc]);

                dag.mask_values[cur_vertex][loc] = set_val;
            }
        }
        undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
        undo_values.push_back(dag.path[cur_vertex][cur_byte]);
        dag.path[cur_vertex][cur_byte] = vertex_2;
        dag.recalculate_preimage(undo_locations,undo_values,cur_vertex);
        dag.update_candidate_locations_good(undo_locations,undo_values,cur_vertex, byte_order, byte_index, vertex_2, source_opt);
        if(dag.check_valid(undo_locations,undo_values,desired, vertex_2, cur_byte)){
            if(backtracking_recursive(desired, byte_order, byte_index, vertex_2, depth+1,dag)){
                return true;
            }
        }
        for(int i = 0; i < undo_locations.size(); i++){
            *undo_locations[i] = undo_values[i];
        }
        
        clear_bit(candidate_pre_locs,source_opt);
    }
    return false;
}

void print_info(vector<uint16_t> &byte_order,uint16_t byte_index,uint16_t cur_vertex,uint16_t depth,DAG &dag){
    for(int i =2; i < dag.vertices; i++){
        if(dag.instructions[i] !=0xFFFF)
            cout << i << "," << instr_list[dag.instructions[i]].name << "\n";
        else{
            cout << i << "," << "UNNEEDED" << "\n";
        }
    }
    for(int i = 0; i < dag.vertices; i++){
        for(int j =0 ;j < byte_index; j++){
            cout << i << "," << j << "," << dag.candidate_locations[i][j] << "\n";
        }
    }
}

bool backtracking_recursive(shuffle_val &desired,
                            vector<uint16_t> &byte_order,
                            uint16_t byte_index,
                            uint16_t cur_vertex,
                            uint16_t depth,
                            DAG &dag 
){
    uint16_t cur_byte = byte_order[byte_index];
    //cout << byte_order.size() << "," << byte_index << "," << depth << "," << cur_vertex << "\n" << flush;

    //Diagnostics
    // for(int i =0; i < byte_index; i++){
    //     uint16_t temp_byte = byte_order[i];
    //     uint16_t input_loc = desired.output[temp_byte];
    //     if(input_loc<16){
    //         assert(dag.candidate_locations[0][temp_byte] == 1 << input_loc);
    //     }else{
    //         assert(dag.candidate_locations[1][temp_byte] == 1 << (input_loc-16));
    //     }

    //     uint16_t temp_vertex = dag.vertices-1;
    //     while(temp_vertex!=0 && temp_vertex !=1){
    //         assert(__builtin_popcount(dag.candidate_locations[temp_vertex][temp_byte]) ==1);
    //         assert(dag.path[temp_vertex][temp_byte] != 0xFFFF);
    //         temp_vertex = dag.path[temp_vertex][temp_byte];
    //     }
    //     assert(__builtin_popcount(dag.candidate_locations[temp_vertex][temp_byte]) ==1);
    // }
    // uint16_t temp_vertex = dag.vertices-1;
    // while(temp_vertex != cur_vertex){
    //     assert(__builtin_popcount(dag.candidate_locations[temp_vertex][cur_byte]) ==1);
    //     if(dag.path[temp_vertex][cur_byte]== 0xFFFF){
    //         cout << "ERROR PATH: "<< temp_vertex << "," << cur_byte << "\n" << flush;
    //     }
    //     assert(dag.path[temp_vertex][cur_byte] != 0xFFFF);
    //     temp_vertex = dag.path[temp_vertex][cur_byte];
    // }
    // assert(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte]) <=1);


    if(cur_vertex ==0 || cur_vertex==1){
        uint16_t cur_byte = byte_order[byte_index];
        uint16_t input_loc = desired.output[cur_byte];
        // if(input_loc < 16){
        //     if(dag.candidate_locations[0][cur_byte] != 1 << input_loc){
        //         assert(__builtin_popcount(dag.candidate_locations[0][cur_byte])==1);
        //         cout << __builtin_ctz(dag.candidate_locations[0][cur_byte]) << "," << input_loc << "\n" << flush;
        //         print_info(byte_order, byte_index, cur_vertex, depth, dag);
        //         throw invalid_argument("ERROR");
        //         return false;  
        //     }

        // }else{
        //     if(dag.candidate_locations[1][cur_byte] != 1 << (input_loc-16)){
        //         assert(__builtin_popcount(dag.candidate_locations[1][cur_byte])==1);
        //         cout << __builtin_ctz(dag.candidate_locations[1][cur_byte]) << "," << input_loc-16 << "\n" << flush;

        //         print_info(byte_order, byte_index, cur_vertex, depth, dag);
        //         throw invalid_argument("ERROR");
        //         return false;
        //     }

        // }
        if(byte_index == byte_order.size()-1){
            return true;
        }else{
            //TODO: Update byte_order
            byte_index+=1;
            cur_vertex = dag.vertices-1;
            //cout << "CHANGED TO \n";
            //cout << byte_order.size() << "," << byte_index << "," << depth << "," << cur_vertex << "\n" << flush;
            cur_byte = byte_order[byte_index];
        }
    }
    cur_byte = byte_order[byte_index];


    
    //Updated, cur_byte now means the index in output vector
    uint16_t cur_byte_old = desired.output[cur_byte];
    //The old version of cur_byte. This used to be the input byte value!


    //assert(cur_byte==byte_index);
    if(dag.instructions[cur_vertex] != 0xFFFF){ //Enumerate mask values only
        int i = dag.instructions[cur_vertex];
        instr inst = instr_list[dag.instructions[cur_vertex]];
        if(inst.type==0){
            //cout << "Entered case 1 unary 0" << inst.name <<"\n" << flush;
            //return unary_nomask(desired, byte_order, byte_index, vertex_order, depth, dag, i, cur_vertex, cur_byte);
            uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
            vector<uint16_t*> undo_locations;
            vector<uint16_t> undo_values;

            undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
            undo_values.push_back(dag.path[cur_vertex][cur_byte]);

            dag.path[cur_vertex][cur_byte] = vertex_1;
            if(backtracking_recursive(desired,byte_order, byte_index,vertex_1,depth+1,dag))
                return true;
            else{
                for(int i = 0; i < undo_locations.size(); i++){
                    *undo_locations[i] = undo_values[i];
                }
                return false;
            }

        }else if(inst.type==1 || inst.type==2){
            //cout << "Entered case 1 unary 1/2" << inst.name <<"\n" << flush;
            //return unary_mask(desired, byte_order, byte_index, vertex_order, depth, dag, i, cur_vertex, cur_byte);
            vector<uint16_t*> undo_locations;
            vector<uint16_t> undo_values;
            uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
            undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
            undo_values.push_back(dag.path[cur_vertex][cur_byte]);
            dag.path[cur_vertex][cur_byte] = vertex_1;
            
            if(unary_mask_new(desired, byte_order, byte_index, depth, dag, cur_vertex, cur_byte))
                return false;
            else{
                for(int i = 0; i < undo_locations.size(); i++){
                    *undo_locations[i] = undo_values[i];
                }
                return false;
            }
        }else if(inst.type==3){
            //cout << "Entered case 1 binary 3" << inst.name <<"\n" << flush;
            uint16_t vertex_1;
            uint16_t vertex_2;
            vector<uint16_t*> undo_locations;
            vector<uint16_t> undo_values;
            if(dag.binary_order[cur_vertex]==0){
                vertex_1 = dag.reverse_edges[cur_vertex][0];
                vertex_2 = dag.reverse_edges[cur_vertex][1];
            }else if(dag.binary_order[cur_vertex]==1){
                vertex_1 = dag.reverse_edges[cur_vertex][1];
                vertex_2 = dag.reverse_edges[cur_vertex][0];
            }else{
                throw invalid_argument("UNREACHABLE");
            }
            //assert(__builtin_popcount(dag.candidate_locations[cur_vertex][cur_byte])==1);
            uint16_t cur_loc = __builtin_ctz(dag.candidate_locations[cur_vertex][cur_byte]);
            undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
            undo_values.push_back(dag.path[cur_vertex][cur_byte]);
            if(__builtin_popcount(dag.valid_preimage_1[cur_vertex][cur_loc]==0)){
                //assert(__builtin_popcount(dag.valid_preimage_2[cur_vertex][cur_loc])==1);
                dag.path[cur_vertex][cur_byte] = vertex_2;
                //cout << "Changed path "<< cur_vertex <<"," << cur_byte << " to "<< vertex_2<<"\n" << flush;
                if(backtracking_recursive(desired, byte_order, byte_index, vertex_2, depth+1, dag))
                    return true;
                else{
                    for(int i = 0; i < undo_locations.size(); i++){
                        *undo_locations[i] = undo_values[i];
                    }
                }
            }else{
                //assert(__builtin_popcount(dag.valid_preimage_1[cur_vertex][cur_loc])==1);
                dag.path[cur_vertex][cur_byte] = vertex_1;
                //cout << "Changed path "<< cur_vertex <<"," << cur_byte << " to "<< vertex_1<<"\n" << flush;
                
                if(backtracking_recursive(desired, byte_order, byte_index, vertex_1, depth+1, dag))
                    return true;
                else{
                    for(int i = 0; i < undo_locations.size(); i++){
                        *undo_locations[i] = undo_values[i];
                    }
                }            
            }
            //return binary_nomask(desired,byte_order,byte_index,vertex_order,depth,dag,i,cur_vertex,cur_byte);
        }else if(inst.type==4 || inst.type==5){
            //cout << "Entered case 1 binary 4/5" << inst.name <<"\n" << flush;
            return binary_mask_new(desired, byte_order, byte_index, depth, dag, cur_vertex, cur_byte);

        }
        else{
                throw invalid_argument("UNREACHABLE");
        }
                
    }else{ //Enumerate instructions AND  mask values

        if(dag.inst_type[cur_vertex]){ //Unary instruction
            for(int i =0; i < 68; i++){
                // if(cur_vertex==4)
                //     cout << i << "\n" << flush;
                //cout << "VERTEX NUM: " << cur_vertex << ", " << i << "\n" << flush;
                dag.instructions[cur_vertex] = i;
                instr inst = instr_list[i];
                
                if(inst.type==0){
                    //cout << "Entered case 2 unary 0" << inst.name <<"\n" << flush;
                    uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
                    vector<uint16_t*> undo_locations;
                    vector<uint16_t> undo_values;
                    undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
                    undo_values.push_back(dag.path[cur_vertex][cur_byte]);
                    dag.path[cur_vertex][cur_byte] = vertex_1;
                    if(unary_nomask_new(desired, byte_order, byte_index, depth, dag, cur_vertex, cur_byte))
                        return true;
                    else{
                        for(int i = 0; i < undo_locations.size(); i++){
                            *undo_locations[i] = undo_values[i];
                        }
                    }
                    
                }else if(inst.type==1 || inst.type==2){
                    //cout << "Entered case 2 unary 1/2" << inst.name <<"\n" << flush;
                    vector<uint16_t*> undo_locations;
                    vector<uint16_t> undo_values;
                    uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
                    undo_locations.push_back(&dag.path[cur_vertex][cur_byte]);
                    undo_values.push_back(dag.path[cur_vertex][cur_byte]);
                    dag.path[cur_vertex][cur_byte] = vertex_1;
                    dag.recalculate_preimage(undo_locations,undo_values,cur_vertex);
                    if(unary_mask_new(desired, byte_order, byte_index, depth, dag, cur_vertex, cur_byte))
                        return true;
                    for(int i = 0; i < undo_locations.size(); i++){
                        *undo_locations[i] = undo_values[i];
                    }
                
                }else{
                    throw invalid_argument("UNREACHABLE");
                }
            }
            dag.instructions[cur_vertex] = 0xFFFF;
            return false;
        }else{ //binary instruction
            for(int i = instr_binary_point; i < num_instructions; i++){
                //cout << "VERTEX NUM: " << cur_vertex << ", " << i << "\n" << flush;
                
                dag.instructions[cur_vertex] = i;
                instr inst = instr_list[i];
                //cout << inst.name << "\n" << flush;
                if(inst.type==3){
                    //cout << "Entered case 2 binary 3" << inst.name << "\n" << flush;
                    if(binary_nomask_new(desired, byte_order, byte_index, depth, dag, cur_vertex, cur_byte))
                        return true;

                }else if(inst.type==4 || inst.type==5){
                    //cout << "Entered case 2 binary 4/5" << inst.name << "\n" << flush;
                    vector<uint16_t*> undo_locations;
                    vector<uint16_t> undo_values;
                    undo_locations.push_back(&dag.binary_order[cur_vertex]);
                    undo_values.push_back(2);
                    dag.recalculate_preimage(undo_locations,undo_values,cur_vertex);
                    for(uint16_t binary_ordering = 0; binary_ordering < 2; binary_ordering++){
                        dag.binary_order[cur_vertex] = binary_ordering;
                        
                        if(binary_mask_new(desired, byte_order, byte_index, depth, dag, cur_vertex, cur_byte))
                            return true;   
                    }
                    for(int i = 0; i < undo_locations.size(); i++){
                        *undo_locations[i] = undo_values[i];
                    }
                    
                }else{
                    throw invalid_argument("UNREACHABLE");
                }
            }
            dag.instructions[cur_vertex] = 0xFFFF;
            return false;
        }
    }
    return false;//just in case
    
                        
}

void backtracking(shuffle_val desired){
    //First, find which bytes we care about in the output
    unordered_map<uint16_t,uint16_t> relevant_bytes;
    for(uint16_t i =0; i < desired.vector_width/8;i++){
        relevant_bytes[desired.output[i]] = i;
    }
    uint64_t previous = timeSinceEpochMillisec();
    //Now, perform backtracking
    for(uint16_t index=113; index < dag_order.size();index++){
        uint16_t i = dag_order[index];
        uint64_t now = timeSinceEpochMillisec();
        // if(i==5 || i==38 || i==35 || i==34 || i==33 || i==43 || i==32)
        //     continue;
        //cout << "Dag Number:" << i << "\n" << flush;
        cout << "Dag Number:" << i << " " << now-previous<<"\n" << flush;
        previous = now;
        vector<uint16_t> byte_order;
        DAG dag = dags[i];
        uint16_t num_vertices = dag.vertices;

        for(int i =0;i<16;i++){
            byte_order.push_back(i);
        }


        bool valid = backtracking_recursive(desired, byte_order,0, num_vertices-1,1,dag);
        if(valid){
            dag.print_state();
            
        }

    }


    // for(int i =0; i < dags.size(); i++){ 
    //     DAG cur = dags[i];
    //     for (int j = 0; j < cur.vertices; j++){ 
    //         //TODO
    //     }
    // }
}

void backtracking_old(shuffle_val desired){
    //First, find which bytes we care about in the output
    unordered_map<uint16_t,uint16_t> relevant_bytes;
    for(uint16_t i =0; i < desired.vector_width/8;i++){
        relevant_bytes[desired.output[i]] = i;
    }
    uint64_t previous = timeSinceEpochMillisec();
    uint16_t earliest = 10;
    //Now, perform backtracking
    for(unsigned int num_insts = 1; num_insts < 5; num_insts ++ ){
        unsigned int num_vertices = num_insts + 2;
        //Enumerating number of vertices
        for(unsigned int i = dag_vertices_to_index[num_vertices]; i < dag_vertices_to_index[num_vertices+1]; i++){
            //Enumerating DAGS
            // if( i==5 ||i==38 || i==35 || i==34 || i==33 || i==43 || i==32)
            //     continue;
            uint64_t now = timeSinceEpochMillisec();

            cout << "Dag Number:" << i << " " << now-previous<<"\n" << flush;
            previous = now;
            vector<uint16_t> byte_order;
            DAG dag = dags[i];
            for(int j =2;j<dag.vertices;j++){
                if(dag.reverse_edges[j].size()==1){
                    cout << dag.reverse_edges[j][0] <<"\n"<< flush;
                }else if(dag.reverse_edges[j].size()==2){
                    cout << dag.reverse_edges[j][0] << "," << dag.reverse_edges[j][1] <<"\n"<< flush;
                }else{
                    cout << "ERROR" << "\n" << flush;
                }
            }

            for(int i =0;i<16;i++){
                byte_order.push_back(i);
            }


            bool valid = backtracking_recursive(desired,byte_order,0, num_vertices-1,1,dag);
            if(valid){
                //cout << num_insts;
                dag.print_state(); 
                //return;
                //dag.print_state();               
            }

        }
    }
    //cout << counter;
    //cout << "4";

    // for(int i =0; i < dags.size(); i++){ 
    //     DAG cur = dags[i];
    //     for (int j = 0; j < cur.vertices; j++){ 
    //         //TODO
    //     }
    // }
}


int main(int argc, char** argv){
    uint16_t max_depth =3;
    read_constraints();
    //cout << "Finished reading constraints\n" << flush;
    read_dags(max_depth);
    //cout << "Finished reading dags\n" << flush;

    for(int i =0; i < num_instructions;i++){
        //cout << i << ":" << instr_list[i].type << "," << instr_list[i].name << "," <<instr_list[i].constraint_length <<"\n";
    }
    for(int i  =0; i < dag_vertices_to_index[max_depth+3];i++){
        DAG dag = dags[i];
        uint16_t num_unary=0;
        uint16_t num_binary=0;
        for(int j =2;j< dag.vertices; j++){
            if(dag.inst_type[j]){
                num_unary++;
            }
            else
                num_binary++;
        }
        // cout << i << ":" << dags[i].distance << "," << num_unary << "," << num_binary << "\n" << flush;
        // for(int j =2;j<dag.vertices;j++){
        //     if(dag.reverse_edges[j].size()==1){
        //         cout << dag.reverse_edges[j][0] <<"\n"<< flush;
        //     }else if(dag.reverse_edges[j].size()==2){
        //         cout << dag.reverse_edges[j][0] << "," << dag.reverse_edges[j][1] <<"\n"<< flush;
        //     }else{
        //         cout << "ERROR" << "\n" << flush;
        //     }
        // }
        // cout<< "______________" << "\n"<<flush;
    }

    for(int i =0; i < dag_order.size(); i++){
        //cout << i << ":" << dag_order[i] << "\n" <<flush;
    }
    
    shuffle_val desired;
    desired.binary = true;
    desired.vector_width = 128;
    if(argc==17){
        for(int i =0; i < 16; i++){
            desired.output[i] = (uint16_t)atoi(argv[i+1]);
        }
    }
    else{
        for(int i =0; i < 16; i++){
            desired.output[i] = 31 - 2*i;
        }
    }

 

    backtracking_old(desired);
}