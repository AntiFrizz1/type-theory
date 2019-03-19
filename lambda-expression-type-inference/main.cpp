#include <iostream>
#include "trees.h"
#include "parser.tab.h"
#include <vector>
#include <map>
#include <set>

extern node* tree;

using  namespace std;

int type_count = 0;

string get_new_type() {
    string ans = "t" + to_string(type_count);
    type_count++;
    return ans;
}

map<string, shared_ptr<type>> types1;

pair<vector<pair<shared_ptr<type>, shared_ptr<type>>>, shared_ptr<type>> make(node* now) {
    application* application1;
    variable* variable1;
    abstraction* abstraction1;

    if ((application1 = dynamic_cast<application *>(now))) {
        string t = get_new_type();
        shared_ptr<value> type1(new value(t));

        pair<vector<pair<shared_ptr<type>, shared_ptr<type>>>, shared_ptr<type>> p1 = make(application1->left);
        pair<vector<pair<shared_ptr<type>, shared_ptr<type>>>, shared_ptr<type>> p2 = make(application1->right);

        vector<pair<shared_ptr<type>, shared_ptr<type>>> vec;

        p1.first.insert(p1.first.end(), p2.first.begin(), p2.first.end());
        p1.first.emplace_back(p1.second, new implication(p2.second, type1));

        return make_pair(p1.first, type1);
    } else if ((abstraction1 = dynamic_cast<abstraction *>(now))) {
        shared_ptr<type> old = nullptr;
        if (types1.count(abstraction1->var) > 0) {
            old = types1[abstraction1->var];
        }
        shared_ptr<type> new_type(new value(get_new_type()));
        types1[abstraction1->var] = new_type;
        pair<vector<pair<shared_ptr<type>, shared_ptr<type>>>, shared_ptr<type>> p1 = make(abstraction1->expression);
        if (old != nullptr) {
            types1[abstraction1->var] = old;
        } else {
            types1.erase(abstraction1->var);
        }
        return make_pair(p1.first, make_shared<implication>(new implication(new_type, p1.second)));
    } else if ((variable1 = dynamic_cast<variable *>(now))) {
        if (types1.count(variable1->var) > 0) {
            return make_pair(vector<pair<shared_ptr<type>, shared_ptr<type>>>(), types1[variable1->var]);
        } else {
            types1[variable1->var] = make_shared<value>(new value(get_new_type()));
            return make_pair(vector<pair<shared_ptr<type>, shared_ptr<type>>>(), types1[variable1->var]);
        }
    }
    return pair<vector<pair<shared_ptr<type>, shared_ptr<type>>>, shared_ptr<type>>();
}

vector<string> ans;
map<string, shared_ptr<type>> types2;
set<string> free_vars;
string free_types;
shared_ptr<type> make_ans(node* now, vector<pair<shared_ptr<type>, shared_ptr<type>>> &s, int level, vector<string> &local) {
    string output;
    for (int i = 0; i < level; i++) {
        output += "*   ";
    }
    application* application1;
    variable* variable1;
    abstraction* abstraction1;
    output += free_types;
    if ((application1 = dynamic_cast<application *>(now))) {
        string t = get_new_type();
        shared_ptr<type> type1(new value(t));
        vector<string> new_vec1;
        vector<string> new_vec2;
        shared_ptr<type> p1 = make_ans(application1->left, s, level + 1, new_vec1);
        shared_ptr<type> p2 = make_ans(application1->right, s, level + 1, new_vec2);

        bool f = false;

        for (auto &j: types2) {
            if (free_vars.count(j.first) == 0) {
                output += j.first + " : " + j.second->to_string() + ", ";
            }
        }

        if (!types2.empty() || !free_types.empty()) {
            output = output.substr(0, output.size() - 2) + " ";
        }

        for (auto &j: s) {
            if (type1->equals(j.first)) {
                type1 = j.second;
            } else {
                shared_ptr<value> tmp;
                if ((tmp = dynamic_pointer_cast<value>(j.first))) {
                    type1->replace(tmp->val, j.second);
                }
            }
        }
        output += "|- ";
        output += now->to_string() + " : " + type1->to_string() + " [rule #2]";

        local.insert(local.end(), new_vec2.begin(), new_vec2.end());
        local.insert(local.end(), new_vec1.begin(), new_vec1.end());

        local.push_back(output);
        return type1;
    } else if ((abstraction1 = dynamic_cast<abstraction *>(now))) {
        shared_ptr<type> old = nullptr;

        if (types2.count(abstraction1->var) > 0) {
            old = types2[abstraction1->var];
        }

        shared_ptr<type> new_type(new value(get_new_type()));
        for (auto &j: s) {
            if (new_type->equals(j.first)) {
                new_type = j.second;
            } else {
                shared_ptr<value> tmp;
                if ((tmp = dynamic_pointer_cast<value>(j.first))) {
                    new_type->replace(tmp->val, j.second);
                }
            }
        }

        types2[abstraction1->var] = new_type;
        shared_ptr<type> p1 = make_ans(abstraction1->expression, s, level + 1, local);

        if (old != nullptr) {
            types2[abstraction1->var] = old;
        } else {
            types2.erase(abstraction1->var);
        }

        bool f = false;

        for (auto &j: types2) {
            if (free_vars.count(j.first) == 0) {
                output += j.first + " : " + j.second->to_string() + ", ";
            }
        }

        if (!types2.empty() || !free_types.empty()) {
            output = output.substr(0, output.size() - 2) + " ";
        }

        shared_ptr<type> type1(new implication(new_type, p1));

        for (auto &j: s) {
            if (type1->equals(j.first)) {
                type1 = j.second;
            } else {
                shared_ptr<value> tmp;
                if ((tmp = dynamic_pointer_cast<value>(j.first))) {
                    type1->replace(tmp->val, j.second);
                }
            }
        }

        output += "|- ";
        output += now->to_string() + " : " + type1->to_string() + " [rule #3]";
        local.push_back(output);

        return type1;
    } else if ((variable1 = dynamic_cast<variable *>(now))) {
        if (types2.count(variable1->var) > 0) {
            shared_ptr<type> type1 = types2[variable1->var];

            bool f = false;

            for (auto &j: types2) {
                if (free_vars.count(j.first) == 0) {
                    output += j.first + " : " + j.second->to_string() + ", ";
                }
            }

            if (!types2.empty() || !free_types.empty()) {
                output = output.substr(0, output.size() - 2) + " ";
            }

            for (auto &j: s) {
                if (type1->equals(j.first)) {
                    type1 = j.second;
                } else {
                    shared_ptr<value> tmp;
                    if ((tmp = dynamic_pointer_cast<value>(j.first))) {
                        type1->replace(tmp->val, j.second);
                    }
                }
            }

            output += "|- ";
            output += now->to_string() + " : " + type1->to_string() + " [rule #1]";
            local.push_back(output);
            return type1;
        } else {
            shared_ptr<type> new_type(new value(get_new_type()));
            for (auto &j: s) {
                if (new_type->equals(j.first)) {
                    new_type = j.second;
                } else {
                    shared_ptr<value> tmp;
                    if ((tmp = dynamic_pointer_cast<value>(j.first))) {
                        new_type->replace(tmp->val, j.second);
                    }
                }
            }
            types2[variable1->var] = new_type;
            shared_ptr<type> type1 = types2[variable1->var];

            bool f = false;

            for (auto &j: types2) {
                if (free_vars.count(j.first) == 0) {
                    output += j.first + " : " + j.second->to_string() + ", ";
                }
            }

            if (!types2.empty() || !free_types.empty()) {
                output = output.substr(0, output.size() - 2) + " ";
            }

            for (auto &j: s) {
                if (type1->equals(j.first)) {
                    type1 = j.second;
                } else {
                    shared_ptr<value> tmp;
                    if ((tmp = dynamic_pointer_cast<value>(j.first))) {
                        type1->replace(tmp->val, j.second);
                    }
                }
            }

            output += "|- ";
            output += now->to_string() + " : " + type1->to_string() + " [rule #1]";
            local.push_back(output);
            return type1;
        }
    }
    return nullptr;
}

vector<pair<shared_ptr<type>, shared_ptr<type>>> old;
vector<pair<shared_ptr<type>, shared_ptr<type>>> newOld;
void recursive(shared_ptr<type> first, shared_ptr<type> second) {
    shared_ptr<value> val1 = nullptr;
    shared_ptr<value> val2 = nullptr;

    shared_ptr<implication> val11 = nullptr;
    shared_ptr<implication> val22 = nullptr;

    int id1 = 0, id2 = 0;

    if ((val1 = dynamic_pointer_cast<value>(first))) {
        id1 = 1;
    } else {
        val11 = dynamic_pointer_cast<implication>(first);
        id1 = 2;
    }

    if ((val2 = dynamic_pointer_cast<value>(second))) {
        id2 = 1;
    } else {
        val22 = dynamic_pointer_cast<implication>(second);
        id2 = 2;
    }

    if (id1 == 1) {
        if (id2 == 1) {
            old.emplace_back(val1, val2);
        } else {
            old.emplace_back(val1, val22);
        }
    } else {
        if (id2 == 1) {
            old.emplace_back(val2, val11);
        } else {
            recursive(val11->left, val22->left);
            recursive(val11->right, val22->right);
        }
    }

}

bool changed = false;
pair<bool, bool> process_line(shared_ptr<type> first, shared_ptr<type> second, int i) {
    if (first->equals(second)) {
        swap(old[i], old[old.size() - 1]);
        old.pop_back();
        changed = true;
        return make_pair(true, true);
    } else {
        shared_ptr<value> val1;
        shared_ptr<value> val2;
        if (!((val1 = dynamic_pointer_cast<value>(first))) && ((val2 = dynamic_pointer_cast<value>(second)))) {
            old[i] = make_pair(second, first);
            changed = true;
            return make_pair(true, false);
        } else if ((val1 = dynamic_pointer_cast<value>(first))) {
            if (second->contains(val1->val)) {
                return make_pair(false, false);
            }
            int n = static_cast<int>(old.size());
            for (int j = 0; j < n; j++) {
                if (i == j) {
                    continue;
                }
                shared_ptr<type> a = old[j].first->copy();
                shared_ptr<type> b = old[j].second->copy();

                bool change = false;

                shared_ptr<value> value1;
                shared_ptr<value> value2;
                if (((value1 = dynamic_pointer_cast<value>(a))) && (value1->val == val1->val)) {
                    a = second;
                    change = true;
                } else if (a->contains(val1->val)) {
                    a->replace(val1->val, second);
                    change = true;
                }

                if (((value2 = dynamic_pointer_cast<value>(b))) && (value2->val == val1->val)) {
                    b = second;
                    change = true;
                } else if (b->contains(val1->val)) {
                    b->replace(val1->val, second);
                    change = true;
                }
                if (change) {
                    old[j] = make_pair(a, b);
                    changed = true;
                }
            }
            return make_pair(true, false);
        } else {
            changed = true;
            swap(old[i], old[old.size() - 1]);
            old.pop_back();
            recursive(first, second);
            return make_pair(true, true);
        }
    }
}


int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);
    yyparse();
    pair<vector<pair<shared_ptr<type>, shared_ptr<type>>>, shared_ptr<type>> a = make(tree);
    old = a.first;
    bool f = true;
    while (true) {
        changed = false;
        for (int i = 0; i < old.size(); i++) {
            pair<bool, bool> ans = process_line(old[i].first, old[i].second, i);
            if (!ans.first) {
                f = false;
                break;
            }
            if (ans.second) {
                i--;
            }
        }
        /*while (!newOld.empty()) {
            old.push_back(newOld[newOld.size() - 1]);
            newOld.pop_back();
        }*/
        if (!changed) {
            break;
        }

        if (!f) {
            break;
        }
    }
    if (f) {
        type_count = 0;
        vector<pair<string, shared_ptr<type>>> free_;
        for (auto &j: types1) {
            free_vars.insert(j.first);
            shared_ptr<type> type1 = j.second;
            for (auto &p: old) {
                if (type1->equals(p.first)) {
                    type1 = p.second;
                } else {
                    shared_ptr<value> tmp;
                    if ((tmp = dynamic_pointer_cast<value>(p.first))) {
                        type1->replace(tmp->val, p.second);
                    }
                }
            }
            free_.emplace_back(j.first, type1);
        }
        types1.clear();
        for (auto &j: free_) {
            free_types += j.first + " : " + j.second->to_string() + ", ";
        }
        shared_ptr<type> a1 = make_ans(tree, old, 0, ans);
        for (int i = 0; i < ans.size(); i++) {
            cout << ans[ans.size() - i - 1] << "\n";
        }
    } else {
        cout << "Expression has no type";
    }
    return 0;
}
