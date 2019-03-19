#include <utility>

#include <string>
#include <utility>
#include <memory>

class node{
public:
    virtual std::string to_string() = 0;
};


class application: public node {
public:
    node* left = nullptr;
    node* right = nullptr;

    application(node* left, node* right) {
        this->left = left;
        this->right = right;
    }

    std::string to_string() override{
        return "(" + left->to_string() + " " + right->to_string() + ")";
    }

};

class abstraction: public node {
public:
    std::string var;
    node* expression;

    abstraction(std::string var, node* expression) {
        this->var = std::move(var);
        this->expression = expression;
    }

    std::string to_string() override{
        return "(\\" + var + "." + expression->to_string() + ")";
    }
};

class variable: public node {
public:
    std::string var;

    variable(std::string var) {
        this->var = std::move(var);
    }

    std::string to_string() override{
        return var;
    }
};

class type {
public:
    type() = default;

    virtual bool equals(std::shared_ptr<type> elem) = 0;

    virtual std::string to_string() = 0;

    virtual bool contains(std::string &val) = 0;

    virtual void replace(std::string &from, std::shared_ptr<type> to) = 0;

    virtual std::shared_ptr<type> copy() = 0;
};

class value: public type {
public:
    std::string val;

    value(std::string val) {
        this->val = std::move(val);
    }

    value(value* value1) {
        this->val = value1->val;
        delete(value1);
    }

    bool equals(std::shared_ptr<type> elem) override {
        std::shared_ptr<value> element;
        return ((element = std::dynamic_pointer_cast<value>(elem))) && (element->val == this->val);
    }

    std::string to_string() override {
        return val;
    }

    bool contains(std::string &val) override {
        return this->val == val;
    }

    void replace(std::string &from, std::shared_ptr<type> to) override {
    }

    std::shared_ptr<type> copy() override {
        return std::make_shared<value>(new value(val));
    }
};

class implication: public type {
public:
    std::shared_ptr<type> left = nullptr;
    std::shared_ptr<type> right = nullptr;

    implication(std::shared_ptr<type> left, std::shared_ptr<type> right) {
        this->left = std::move(left);
        this->right = std::move(right);
    }

    implication(implication* implication1) {
        this->left = implication1->left;
        this->right = implication1->right;
        delete(implication1);
    }

    bool equals(std::shared_ptr<type> elem) override {
        std::shared_ptr<implication> element;
        return ((element = std::dynamic_pointer_cast<implication>(elem))) && left->equals(element->left) && right->equals(element->right);
    }

    std::string to_string() override {
        return "(" + left->to_string() + " -> " + right->to_string() + ")";
    }

    bool contains(std::string &val) override {
        return left->contains(val) || right->contains(val);
    }

    std::shared_ptr<type> copy() override {
        return  std::make_shared<implication>(new implication(left->copy(), right->copy()));
    }

    void replace(std::string &from, std::shared_ptr<type> to) override {
        std::shared_ptr<value> a = nullptr;
        if ((a = std::dynamic_pointer_cast<value>(left))) {
            if (a->val == from) {
                left = to->copy();
            }
        } else {
            left->replace(from, to);
        }

        if ((a = std::dynamic_pointer_cast<value>(right))) {
            if (a->val == from) {
                right = to->copy();
            }
        } else {
            right->replace(from, to);
        }
    }
};
