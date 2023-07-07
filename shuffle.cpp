#include <fstream>
#include <iostream>
#include <vector>
#include <bits/stdc++.h>
using namespace std;

const uint16_t MAX_VERTICES = 10;
const uint32_t MAX_INSTRUCTIONS = 2000;

typedef unsigned __int128 uint128_t;
typedef struct shuffle_val {
    bool binary;
    uint16_t vector_width;
    uint16_t output[64]; // For each of the bytes in up to 512 bits, store byte num from input. Uses only the first 2^i for smaller vector width or larger packed values.

} shuffle_val;

typedef struct constraint {
    uint16_t source;
    uint16_t target;
    unordered_map<uint16_t, uint16_t> map;
} constraint;

typedef struct instr {
    string name;
    uint16_t type; //0 = unary no mask, 1 = unary constant mask, 2 = unary register mask, 3 = binary no mask, 4 = binary constant mask, 5 = binary register mask
    uint16_t vector_width;
    uint16_t mask_position; //0,1,2

    uint32_t constraint_length;
    constraint* constraints;
    
} instr;
struct hash_pair { //Custom hash function for pairs, copy pasted from stack overflow
    template <class T1, class T2>
    size_t operator()(const pair<T1, T2>& p) const
    {
        auto hash1 = hash<T1>{}(p.first);
        auto hash2 = hash<T2>{}(p.second);
 
        if (hash1 != hash2) {
            return hash1 ^ hash2;             
        }
         
        // If hash1 == hash2, their XOR is zero.
          return hash1;
    }
};
instr instr_list[MAX_INSTRUCTIONS];
array<vector<unordered_set<uint16_t>>,MAX_INSTRUCTIONS> instr_valid_map;
array<unordered_map<pair<uint16_t,uint16_t>,constraint, hash_pair>,MAX_INSTRUCTIONS> instr_constraint_maps;

int instr_binary_point=0;
int num_instructions =0;


//Using immutable DAGs in adjacency list format as we simply take in input from pynauty 
class DAG{
public:
    uint16_t vertices;
    uint16_t distance;
    vector<vector<uint16_t>> edges;
    vector<vector<uint16_t>> reverse_edges;
    vector<int> instructions; //This should hold list of indicies into instr_list for each vertex
    vector<unordered_map<uint16_t,uint16_t>> mask_values;
    vector<vector<uint16_t>> intermediates; //Bit representation of intermediates. Each vertex stores mapping of each of 32 bytes from input to location in intermediate.

    bool* inst_type; //true = unary, false = binary, vertices 0,1 defaulted to inputs(type doesn't matter/exist)
    bool* reachable0; //reachable by 1st input
    bool* reachable1; //reachable by 2nd input
    uint16_t* distance0; //Distance to 1st input
    uint16_t* distance1; //Distance to 2nd input
    DAG(uint16_t vertices_in){
        vertices = vertices_in;
        distance = 0;
        edges =  vector<vector<uint16_t>>(vertices);
        reverse_edges =  vector<vector<uint16_t>>(vertices);
        inst_type = new bool[vertices];
        instructions = vector<int>(vertices);
        mask_values = vector<unordered_map<uint16_t,uint16_t>>(vertices);
        intermediates = vector<vector<uint16_t>>(vertices);
        reachable0 = new bool[vertices];
        reachable1 = new bool[vertices];
        distance0 = new uint16_t[vertices];
        distance1 = new uint16_t[vertices];
        for(int i =0; i < vertices; i++){
            mask_values[i] = unordered_map<uint16_t,uint16_t>();
            instructions[i] = 0xFFFF;
            reachable0[i] = false;
            reachable1[i] = false;
            distance0[i] = 0xFFFF;
            distance1[i] = 0xFFFF;
            intermediates[i] = vector<uint16_t>(32);
            for(int j = 0;j<32;j++){
                intermediates[i][j]=16;
            }
        }

    }
    void calculate_reverse_edges(){
        for(int i =0; i < vertices; i++){
            reverse_edges[i] = vector<uint16_t>();
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
            for(int j =0; j < reverse_edges[i].size();j++){
                cout << reverse_edges[i][j] << ",";
            }
            for(auto elem : mask_values[i]){
                cout << elem.first << ":" << elem.second << "\n";
            }
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
        // delete[] edges;
        // delete[] reverse_edges;
        // delete[] inst_type;
    }
};
vector<DAG> dags;
uint32_t dag_vertices_to_index[MAX_VERTICES+1];
void read_dags(){
    ifstream read_file("dag_data.txt");
    uint32_t num_dags;
    read_file >> num_dags;

    dags.reserve(num_dags);
    uint16_t current_vertex = 0;
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
    } 

}
void read_constraints(){
    ifstream read_file("constraint_data3.txt");
    uint32_t num_insts;
    read_file >> num_insts;

    num_instructions = num_insts;

    for(int i =0; i < num_insts;i++){
        instr_valid_map[i] = vector<unordered_set<uint16_t>>(16);
        instr_constraint_maps[i] = unordered_map<pair<uint16_t,uint16_t>,constraint, hash_pair>();
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
            instr_valid_map[i][target].insert(source);

            unordered_map<uint16_t,uint16_t> umap;
            for(int k =0; k < num_constraints; k++){
                uint16_t location;
                uint16_t bit_val;
                read_file >> location >> bit_val;
                umap[location] = bit_val;
            }
            constraint temp = {source, target, umap};
            instr_constraint_maps[i][pair<uint16_t,uint16_t>{source,target}] = temp;
            instr_list[i].constraints[j] = temp;
        }
    }


}


/*
   First Backtracking Algorithm
        - Enumerate over number of instructions
        - Enumerate over number of "difficult"(masked) instructions
        - Enumerate over DAGS within number of instructions
        - Enumerate over OP Codes while going 1 byte at a time()
        - Use constraint table to filter which instructions satisfy which byte movements

*/
bool backtracking_recursive(shuffle_val &desired,
                            unordered_map<uint16_t,uint16_t> &relevant_bytes,
                            vector<uint16_t> byte_order,
                            vector<uint16_t> &vertex_order,
                            DAG &dag 
){
    //Base conditions, if byte order is empty, move onto next vertex. If vertex order is also zero, then done
    
    if(vertex_order.size()==0){
        if(byte_order.size()==1){
            dag.print_state();
            return false;
            //Decide Early stop or not!
            //return true;
        }else{
            byte_order.erase(byte_order.begin());
            vertex_order.push_back(dag.vertices-1);
        }

    }else if(vertex_order.size()>1){
        // for(int x = 0; x < vertex_order.size(); x++){
        //     cout << vertex_order[x] << ",";
        // }
        //cout <<"\n" << flush;
        throw invalid_argument("Vertex order should have size 1 or 0 only");
    }
    //cout << byte_order.size() << " " << vertex_order.size() << "\n" << flush;
    uint16_t cur_vertex = vertex_order[0];
    //cout << "TEST1 " << vertex_order.size() << "," << vertex_order[0] << flush ;
    vertex_order.erase(vertex_order.begin());
    //cout << "TEST2 " << vertex_order.size() << "," << vertex_order[0] << flush ;
    uint16_t cur_byte = byte_order[0];
    if(dag.instructions[cur_vertex] != 0xFFFF){ //Enumerate mask values only
        int i = dag.instructions[cur_vertex];
        instr inst = instr_list[i];
        if(inst.type==0){
            //cout << "Entered case 1 unary 0" << inst.name <<"\n" << flush;
            uint16_t target = dag.intermediates[cur_vertex][cur_byte];
            uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
            if(vertex_1==1 || vertex_1==0){
                uint16_t source;
                if(cur_byte<16)
                    source = cur_byte;
                else
                    source = cur_byte-16;
                if(instr_valid_map[i][target].find(source) != instr_valid_map[i][target].end()){
                    dag.intermediates[vertex_1][cur_byte] = source%16;
                    if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                        return true;
                    }
                }else{
                    dag.intermediates[vertex_1][cur_byte] = 16;
                    return false;
                }
            }
            else{
                for(auto source: instr_valid_map[i][target]){
                    dag.intermediates[vertex_1][cur_byte] = source%16;
                    vertex_order.push_back(vertex_1);
                    if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                        return true;
                    }
                }
                dag.intermediates[vertex_1][cur_byte] = 16;
                return false;
            }

        }else if(inst.type==1 || inst.type==2){
            //cout << "Entered case 1 unary 1/2" << inst.name <<"\n" << flush;
            uint16_t target = dag.intermediates[cur_vertex][cur_byte];
            uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
            if(vertex_1==1 || vertex_1==0){
                uint16_t source;
                if(cur_byte<16)
                    source = cur_byte;
                else
                    source = cur_byte-16;
                if(instr_valid_map[i][target].find(source) != instr_valid_map[i][target].end()){
                    dag.intermediates[vertex_1][cur_byte] = source%16;
                    bool valid = true;
                    unordered_map<uint16_t,uint16_t> undo; //0 or 1, 2 means remove
                    constraint temp = instr_constraint_maps[i][pair<uint16_t,uint16_t>{source, target }];
                    for(auto val : temp.map){
                        
                        if(dag.mask_values[cur_vertex].find(val.first) !=dag.mask_values[cur_vertex].end()){
                            uint16_t former = dag.mask_values[cur_vertex][val.first];
                            undo[val.first] = former;
                            if(val.second != former){
                                //Conflict
                                valid = false;
                                break;
                            }
                        }else{
                            undo[val.first] = 2;
                            dag.mask_values[cur_vertex][val.first]=val.second;
                        }
                    }
                    if(!valid){
                        //Undo first
                        for(auto val: undo){
                            if(val.second==2){
                                dag.mask_values[cur_vertex].erase(val.first);
                            }else{
                                dag.mask_values[cur_vertex][val.first]=val.second;
                            }

                        }
                    }else if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                        return true;
                    }else{
                        dag.intermediates[vertex_1][cur_byte] = 16;
                        for(auto val: undo){
                            if(val.second==2){
                                dag.mask_values[cur_vertex].erase(val.first);
                            }else{
                                dag.mask_values[cur_vertex][val.first]=val.second;
                            }

                        }
                        return false;
                    }
                }else{
                    dag.intermediates[vertex_1][cur_byte] = 16;
                    return false;
                }
            }else{
                for(auto source: instr_valid_map[i][target]){
                    constraint temp = instr_constraint_maps[i][pair<uint16_t,uint16_t>{source, target }];
                    unordered_map<uint16_t,uint16_t> undo; //0 or 1, 2 means remove
                    bool valid = true;
                    for(auto val : temp.map){
                        
                        if(dag.mask_values[cur_vertex].find(val.first) !=dag.mask_values[cur_vertex].end()){
                            uint16_t former = dag.mask_values[cur_vertex][val.first];
                            undo[val.first] = former;
                            if(val.second != former){
                                //Conflict
                                valid = false;
                                break;
                            }
                        }else{
                            undo[val.first] = 2;
                            dag.mask_values[cur_vertex][val.first]=val.second;
                        }
                    }
                    if(!valid){
                        //Undo first
                        for(auto val: undo){
                            if(val.second==2){
                                dag.mask_values[cur_vertex].erase(val.first);
                            }else{
                                dag.mask_values[cur_vertex][val.first]=val.second;
                            }

                        }
                        continue;
                    }
                    dag.intermediates[vertex_1][cur_byte] = source%16;
                    vertex_order.push_back(vertex_1);
                    if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                        return true;
                    }else{
                        for(auto val: undo){
                            if(val.second==2){
                                dag.mask_values[cur_vertex].erase(val.first);
                            }else{
                                dag.mask_values[cur_vertex][val.first]=val.second;
                            }

                        }
                    }
                }
                dag.intermediates[vertex_1][cur_byte] = 16;
                return false;
            }

        }else if(inst.type==3){
            //cout << "Entered case 1 binary 3" << inst.name <<"\n" << flush;
            uint16_t target = dag.intermediates[cur_vertex][cur_byte];
            uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
            uint16_t vertex_2 = dag.reverse_edges[cur_vertex][1];
            bool reachable_1;//= dag.reachable0[vertex_1];
            bool reachable_2;// = dag.reachable0[vertex_2];
            if(cur_byte<16){
                reachable_1 = dag.reachable0[vertex_1];
                reachable_2 = dag.reachable0[vertex_2];
            }else{
                reachable_1 = dag.reachable1[vertex_1];
                reachable_2 = dag.reachable1[vertex_2];
            }
            
            for(auto source: instr_valid_map[i][target]){
                if(source<16 && !reachable_1 || source>=16 && !reachable_2)
                    continue;
                uint16_t vertex;
                if(source<16)
                    vertex = vertex_1;
                else
                    vertex = vertex_2;
                if(vertex == 0 || vertex==1){
                    if(source%16 != cur_byte%16)
                        continue;
                    dag.intermediates[vertex][cur_byte] = source%16;
                    if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                        return true;
                    }
                }else{
                    dag.intermediates[vertex][cur_byte] = source%16;
                    vertex_order.push_back(vertex);
                    if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                        return true;
                    }
                }
            }
            dag.intermediates[vertex_1][cur_byte] = 16;
            return false;
        }else if(inst.type==4 || inst.type==5){
            //cout << "Entered case 1 binary 4/5" << inst.name <<"\n" << flush;
            uint16_t target = dag.intermediates[cur_vertex][cur_byte];
            uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
            uint16_t vertex_2 = dag.reverse_edges[cur_vertex][1];
            bool reachable_1;//= dag.reachable0[vertex_1];
            bool reachable_2;// = dag.reachable0[vertex_2];
            if(cur_byte<16){
                reachable_1 = dag.reachable0[vertex_1];
                reachable_2 = dag.reachable0[vertex_2];
            }else{
                reachable_1 = dag.reachable1[vertex_1];
                reachable_2 = dag.reachable1[vertex_2];
            }
            
            for(auto source: instr_valid_map[i][target]){
                if(source<16 && !reachable_1 || source>=16 && !reachable_2)
                    continue;
                uint16_t vertex;
                if(source<16)
                    vertex = vertex_1;
                else
                    vertex = vertex_2;
                constraint temp = instr_constraint_maps[i][pair<uint16_t,uint16_t>{source, target }];
                unordered_map<uint16_t,uint16_t> undo;
                if(vertex == 0 || vertex==1){
                    if(source%16 != cur_byte%16)
                        continue;
                }
                bool valid = true;
                for(auto val : temp.map){
                    
                    if(dag.mask_values[cur_vertex].find(val.first) !=dag.mask_values[cur_vertex].end()){
                        uint16_t former = dag.mask_values[cur_vertex][val.first];
                        undo[val.first] = former;
                        if(val.second != former){
                            //Conflict
                            valid = false;
                            break;
                        }
                    }else{
                        undo[val.first] = 2;
                        dag.mask_values[cur_vertex][val.first]=val.second;
                    }
                }
                if(!valid){
                    //Undo first
                    for(auto val: undo){
                        if(val.second==2){
                            dag.mask_values[cur_vertex].erase(val.first);
                        }else{
                            dag.mask_values[cur_vertex][val.first]=val.second;
                        }

                    }
                    continue;
                }
                if(vertex==0 || vertex==1){
                    dag.intermediates[vertex][cur_byte] = source%16;
                }else{
                    dag.intermediates[vertex][cur_byte] = source%16;
                    vertex_order.push_back(vertex);
                }
                if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                        return true;
                } else{
                    for(auto val: undo){
                        if(val.second==2){
                            dag.mask_values[cur_vertex].erase(val.first);
                        }else{
                            dag.mask_values[cur_vertex][val.first]=val.second;
                        }

                    }
                }
                
            }
            dag.intermediates[vertex_1][cur_byte] = 16;
            return false;

        }
                
    }else{ //Enumerate instructions AND  mask values

        if(dag.inst_type[cur_vertex]){ //Unary instruction
            for(int i =0; i < instr_binary_point; i++){
                //cout << "VERTEX NUM: " << cur_vertex << ", " << i << "\n" << flush;
                dag.instructions[cur_vertex] = i;
                instr inst = instr_list[i];
                if(dag.mask_values[cur_vertex].size()!=0){
                    cout << inst.name << "," <<inst.type << "," << dag.mask_values[cur_vertex].size() << flush ;
                    throw invalid_argument("mask should be zeroed!");
                }
                if(inst.type==0){
                    //cout << "Entered case 2 unary 0" << inst.name <<"\n" << flush;
                    uint16_t target = dag.intermediates[cur_vertex][cur_byte];
                    uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
                    if(vertex_1==1 || vertex_1==0){
                        uint16_t source;
                        if(cur_byte<16)
                            source = cur_byte;
                        else
                            source = cur_byte-16;
                        if(instr_valid_map[i][target].find(source) != instr_valid_map[i][target].end()){
                            dag.intermediates[vertex_1][cur_byte] = source%16;
                            if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                                return true;
                            }
                        }else{
                            dag.intermediates[vertex_1][cur_byte] = 16;
                        }
                    }
                    else{
                        for(auto source: instr_valid_map[i][target]){
                            dag.intermediates[vertex_1][cur_byte] = source%16;
                            vertex_order.push_back(vertex_1);
                            //cout << "TEST" << vertex_order.size() << "," <<vertex_order[0] << "\n" << flush ;
                            if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                                return true;
                            }
                        }
                        dag.intermediates[vertex_1][cur_byte] = 16;
                    }
                    
                }else if(inst.type==1 || inst.type==2){
                    //cout << "Entered case 2 unary 1/2" << inst.name <<"\n" << flush;
                    uint16_t target = dag.intermediates[cur_vertex][cur_byte];
                    uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
                    if(vertex_1==1 || vertex_1==0){
                        uint16_t source;
                        if(cur_byte<16)
                            source = cur_byte;
                        else
                            source = cur_byte-16;
                        if(instr_valid_map[i][target].find(source) != instr_valid_map[i][target].end()){
                            dag.intermediates[vertex_1][cur_byte] = source%16;
                            bool valid = true;
                            unordered_map<uint16_t,uint16_t> undo; //0 or 1, 2 means remove
                            constraint temp = instr_constraint_maps[i][pair<uint16_t,uint16_t>{source, target }];
                            for(auto val : temp.map){
                                
                                if(dag.mask_values[cur_vertex].find(val.first) !=dag.mask_values[cur_vertex].end()){
                                    uint16_t former = dag.mask_values[cur_vertex][val.first];
                                    undo[val.first] = former;
                                    if(val.second != former){
                                        //Conflict
                                        valid = false;
                                        break;
                                    }
                                }else{
                                    undo[val.first] = 2;
                                    dag.mask_values[cur_vertex][val.first]=val.second;
                                }
                            }
                            if(!valid){
                                //Undo first
                                for(auto val: undo){
                                    if(val.second==2){
                                        dag.mask_values[cur_vertex].erase(val.first);
                                    }else{
                                        dag.mask_values[cur_vertex][val.first]=val.second;
                                    }

                                }
                            }else if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                                return true;
                            }else{
                                dag.intermediates[vertex_1][cur_byte] = 16;
                                for(auto val: undo){
                                    if(val.second==2){
                                        dag.mask_values[cur_vertex].erase(val.first);
                                    }else{
                                        dag.mask_values[cur_vertex][val.first]=val.second;
                                    }

                                }
                            }
                        }else{
                            dag.intermediates[vertex_1][cur_byte] = 16;
                        }
                    }else{
                        for(auto source: instr_valid_map[i][target]){
                            constraint temp = instr_constraint_maps[i][pair<uint16_t,uint16_t>{source, target }];
                            unordered_map<uint16_t,uint16_t> undo; //0 or 1, 2 means remove
                            bool valid = true;
                            for(auto val : temp.map){
                                
                                if(dag.mask_values[cur_vertex].find(val.first) !=dag.mask_values[cur_vertex].end()){
                                    uint16_t former = dag.mask_values[cur_vertex][val.first];
                                    undo[val.first] = former;
                                    if(val.second != former){
                                        //Conflict
                                        valid = false;
                                        break;
                                    }
                                }else{
                                    undo[val.first] = 2;
                                    dag.mask_values[cur_vertex][val.first]=val.second;
                                }
                            }
                            if(!valid){
                                //Undo first
                                for(auto val: undo){
                                    if(val.second==2){
                                        dag.mask_values[cur_vertex].erase(val.first);
                                    }else{
                                        dag.mask_values[cur_vertex][val.first]=val.second;
                                    }

                                }
                                continue;
                            }
                            dag.intermediates[vertex_1][cur_byte] = source%16;
                            vertex_order.push_back(vertex_1);
                            if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                                return true;
                            }else{
                                for(auto val: undo){
                                    if(val.second==2){
                                        dag.mask_values[cur_vertex].erase(val.first);
                                    }else{
                                        dag.mask_values[cur_vertex][val.first]=val.second;
                                    }

                                }
                            }
                        }
                        dag.intermediates[vertex_1][cur_byte] = 16;
                    }
                
                }
            }
            dag.instructions[cur_vertex] = 0xFFFF;
            return false;
        }else{ //binary instruction
            for(int i = instr_binary_point; i < num_instructions; i++){
                //cout << "VERTEX NUM: " << cur_vertex << ", " << i << "\n" << flush;
                dag.instructions[cur_vertex] = i;
                instr inst = instr_list[i];
                if(dag.mask_values[cur_vertex].size()!=0){
                    cout << inst.name << "," <<inst.type << "," << dag.mask_values[cur_vertex].size() << flush ;
                    throw invalid_argument("mask should be zeroed!");
                }
                if(inst.type==3){
                    //cout << "Entered case 2 binary 3" << inst.name << "\n" << flush;
                    uint16_t target = dag.intermediates[cur_vertex][cur_byte];
                    uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
                    uint16_t vertex_2 = dag.reverse_edges[cur_vertex][1];
                    bool reachable_1;//= dag.reachable0[vertex_1];
                    bool reachable_2;// = dag.reachable0[vertex_2];
                    if(cur_byte<16){
                        reachable_1 = dag.reachable0[vertex_1];
                        reachable_2 = dag.reachable0[vertex_2];
                    }else{
                        reachable_1 = dag.reachable1[vertex_1];
                        reachable_2 = dag.reachable1[vertex_2];
                    }
                    
                    for(auto source: instr_valid_map[i][target]){
                        if(source<16 && !reachable_1 || source>=16 && !reachable_2){
                            //cout << "unreachable\n" << flush; 
                            continue;
                        }

                        uint16_t vertex;
                        if(source<16)
                            vertex = vertex_1;
                        else
                            vertex = vertex_2;
                        if(vertex == 0 || vertex==1){
                            if(source%16 != cur_byte%16){
                                //cout << "wrong lane\n" << flush;
                            }
                            dag.intermediates[vertex][cur_byte] = source%16;
                            if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                                return true;
                            }
                        }else{
                            dag.intermediates[vertex][cur_byte] = source%16;
                            vertex_order.push_back(vertex);
                            if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                                return true;
                            }
                        }
                    }
                    dag.intermediates[vertex_1][cur_byte] = 16;

                }else if(inst.type==4 || inst.type==5){
                    //cout << "Entered case 2 binary 4/5" << inst.name << "\n" << flush;
                    uint16_t target = dag.intermediates[cur_vertex][cur_byte];
                    uint16_t vertex_1 = dag.reverse_edges[cur_vertex][0];
                    uint16_t vertex_2 = dag.reverse_edges[cur_vertex][1];
                    bool reachable_1;//= dag.reachable0[vertex_1];
                    bool reachable_2;// = dag.reachable0[vertex_2];
                    if(cur_byte<16){
                        reachable_1 = dag.reachable0[vertex_1];
                        reachable_2 = dag.reachable0[vertex_2];
                    }else{
                        reachable_1 = dag.reachable1[vertex_1];
                        reachable_2 = dag.reachable1[vertex_2];
                    }
                    
                    for(auto source: instr_valid_map[i][target]){

                        if(source<16 && !reachable_1 || source>=16 && !reachable_2)
                            continue;
                        uint16_t vertex;
                        if(source<16)
                            vertex = vertex_1;
                        else
                            vertex = vertex_2;
                        constraint temp = instr_constraint_maps[i][pair<uint16_t,uint16_t>{source, target }];
                        unordered_map<uint16_t,uint16_t> undo;
                        if(vertex == 0 || vertex==1){
                            if(source%16 != cur_byte%16)
                                continue;
                        }
                        //cout << source << " constraints\n" << flush;
                        bool valid = true;
                        for(auto val : temp.map){
                            
                            if(dag.mask_values[cur_vertex].find(val.first) !=dag.mask_values[cur_vertex].end()){
                                uint16_t former = dag.mask_values[cur_vertex][val.first];
                                undo[val.first] = former;
                                if(val.second != former){
                                    //Conflict
                                    valid = false;
                                    break;
                                }
                            }else{
                                undo[val.first] = 2;
                                dag.mask_values[cur_vertex][val.first]=val.second;
                            }
                        }
                        if(!valid){
                            //Undo first
                            for(auto val: undo){
                                if(val.second==2){
                                    dag.mask_values[cur_vertex].erase(val.first);
                                }else{
                                    dag.mask_values[cur_vertex][val.first]=val.second;
                                }

                            }
                            continue;
                        }
                        if(vertex==0 || vertex==1){
                            dag.intermediates[vertex][cur_byte] = source%16;
                        }else{
                            dag.intermediates[vertex][cur_byte] = source%16;
                            vertex_order.push_back(vertex);
                        }
                        if(backtracking_recursive(desired, relevant_bytes, byte_order, vertex_order,dag)){
                                return true;
                        } else{
                            for(auto val: undo){
                                if(val.second==2){
                                    dag.mask_values[cur_vertex].erase(val.first);
                                }else{
                                    dag.mask_values[cur_vertex][val.first]=val.second;
                                }

                            }
                        }
                        
                    }
                    dag.intermediates[vertex_1][cur_byte] = 16;
                }
            }
            dag.instructions[cur_vertex] = 0xFFFF;
            return false;
        }
    }
    return false;//just in case
    
                        
}
uint64_t timeSinceEpochMillisec() {
  using namespace std::chrono;
  return duration_cast<milliseconds>(system_clock::now().time_since_epoch()).count();
}
void backtracking(shuffle_val desired){
    //First, find which bytes we care about in the output
    unordered_map<uint16_t,uint16_t> relevant_bytes;
    for(uint16_t i =0; i < desired.vector_width/8;i++){
        relevant_bytes[desired.output[i]] = i;
    }
    uint64_t previous = timeSinceEpochMillisec();
    //Now, perform backtracking
    for(unsigned int num_insts = 1; num_insts < 5; num_insts ++ ){
        unsigned int num_vertices = num_insts + 2;
        //Enumerating number of vertices
        for(unsigned int i = dag_vertices_to_index[num_vertices]; i < dag_vertices_to_index[num_vertices+1]; i++){
            //Enumerating DAGS
            if(i==5)
                continue;
            uint64_t now = timeSinceEpochMillisec();

            cout << "Dag Number:" << i << " " << now-previous<<"\n" << flush;
            previous = now;
            vector<uint16_t> byte_order;
            DAG dag = dags[i];
            for(auto elem: relevant_bytes){
                dag.intermediates[num_vertices-1][elem.first] = elem.second;
                byte_order.push_back(elem.first);
            }
            vector<uint16_t> vertex_order;
            vertex_order.push_back(num_vertices-1);

            bool valid = backtracking_recursive(desired,relevant_bytes, byte_order, vertex_order,dag);
            if(valid){
                dag.print_state();
                
            }
            for(auto elem: relevant_bytes){
                dag.intermediates[num_vertices-1][elem.first] = 16; //Undo if not valid
            }
        }
    }

    // for(int i =0; i < dags.size(); i++){ 
    //     DAG cur = dags[i];
    //     for (int j = 0; j < cur.vertices; j++){ 
    //         //TODO
    //     }
    // }
}

int main(){
    read_constraints();
    read_dags();

    for(int i =0; i < num_instructions;i++){
        cout << i << ":" << instr_list[i].type << "," << instr_list[i].name << "," <<instr_list[i].constraint_length <<"\n";
    }
    for(int i  =0; i < dag_vertices_to_index[7];i++){
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
        cout << i << ":" << dags[i].distance << "," << num_unary << "," << num_binary << "\n" << flush;
        for(int j =2;j<dag.vertices;j++){
            if(dag.reverse_edges[j].size()==1){
                cout << dag.reverse_edges[j][0] <<"\n"<< flush;
            }else if(dag.reverse_edges[j].size()==2){
                cout << dag.reverse_edges[j][0] << "," << dag.reverse_edges[j][1] <<"\n"<< flush;
            }else{
                cout << "ERROR" << "\n" << flush;
            }
        }
        cout<< "______________" << "\n"<<flush;
    }
    
    shuffle_val desired;
    desired.binary = true;
    desired.vector_width = 128;
    for(int i =0; i < 16; i++){
        desired.output[i] = 31 - 2*i;
    }

    backtracking(desired);
}