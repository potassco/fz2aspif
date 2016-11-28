/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  Main authors:
 *     Guido Tack <tack@gecode.org>
 *
 *  Contributing authors:
 *     Mikael Lagerkvist <lagerkvist@gmail.com>
 *
 *  Copyright:
 *     Guido Tack, 2007
 *     Mikael Lagerkvist, 2009
 *
 *  Last modified:
 *     $Date: 2010-07-02 19:18:43 +1000 (Fri, 02 Jul 2010) $ by $Author: tack $
 *     $Revision: 11149 $
 *
 *  This file is part of Gecode, the generic constraint
 *  development environment:
 *     http://www.gecode.org
 *
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

#include "registry.hh"
#include "flatzinc.hh"
#include "ast.hh"

namespace FlatZinc {

  Registry& registry(void) {
    static Registry r;
    return r;
  }

  void
  Registry::post(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
    std::map<std::string,poster>::iterator i = r.find(ce.id);
    if (i == r.end()) {
      throw FlatZinc::Error("Registry",
        std::string("Constraint ")+ce.id+" not found");
    }
    i->second(s, ce, ann);
  }

  void
  Registry::add(const std::string& id, poster p) {
    r[id] = p;
  }

  namespace {

    void print2var(FlatZincModel& s, const ConExpr& ce, AST::Node* ann, const std::string& op)
    {
        s.addOperator(op);
        s.addOperator("linear");
        unsigned int elem = s.getNewElement();
        unsigned int id;
        if (ce[0]->isInt())
            id = s.addInteger(ce[0]->getInt());
        else
            id = s.getIntVariableUid(ce[0]->getIntVar());
        std::cout << "9 4 " << elem << " 1 " << id << " 0\n";
        std::cout << "9 6 " << s.getTrueUid() << " " << s.getOperatorUid("linear") << " ";
        
        if (ce[1]->isInt())
            id = s.addInteger(ce[1]->getInt());
        else
            id = s.getIntVariableUid(ce[1]->getIntVar());
        std::cout << "1" << " " << elem << " " << s.getOperatorUid(op) << " " << id << "\n";        
    }
    
    void print2var_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann, const std::string& op)
    {
        s.addOperator(op);
        s.addOperator("linear");
        unsigned int elem = s.getNewElement();
        unsigned int id;
        if (ce[0]->isInt())
            id = s.addInteger(ce[0]->getInt());
        else
            id = s.getIntVariableUid(ce[0]->getIntVar());
        std::cout << "9 4 " << elem << " 1 " << id << " 0\n";
        std::cout << "9 6 " << s.getBoolVariableUid(ce[2]->getBoolVar()) << " " << s.getOperatorUid("linear") << " ";
        if (ce[1]->isInt())
            id = s.addInteger(ce[1]->getInt());
        else
            id = s.getIntVariableUid(ce[1]->getIntVar());
        std::cout << "1" << " " << elem << " " << s.getOperatorUid(op) << " " << id << "\n";        
    }

    /// a = b
    void p_int_eq(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_eq("<<(*ce[0])<<","<<(*ce[1])<<")::"<<(*ann)<<"\n";
      print2var(s,ce,ann,"=");
    }
    void p_int_ne(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_eq("<<(*ce[0])<<","<<(*ce[1])<<")::"<<(*ann)<<"\n";
      print2var(s,ce,ann,"!=");
    }
    void p_int_ge(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_ge("<<(*ce[0])<<","<<(*ce[1])<<")::"<<(*ann)<<"\n";
      print2var(s,ce,ann,">=");
    }
    void p_int_gt(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_gt("<<(*ce[0])<<","<<(*ce[1])<<")::"<<(*ann)<<"\n";
      print2var(s,ce,ann,">");
    }
    void p_int_le(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_le("<<(*ce[0])<<","<<(*ce[1])<<")::"<<(*ann)<<"\n";
      print2var(s,ce,ann,"<=");
    }
    void p_int_lt(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lt("<<(*ce[0])<<","<<(*ce[1])<<")::"<<(*ann)<<"\n";
      print2var(s,ce,ann,"<");
    }

    /* Comparisons */
    void p_int_eq_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_eq_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print2var_reif(s,ce,ann,"=");
    }
    void p_int_ne_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_ne_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print2var_reif(s,ce,ann,"!=");
    }
    void p_int_ge_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_ge_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print2var_reif(s,ce,ann,">=");
    }
    void p_int_gt_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_gt_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print2var_reif(s,ce,ann,">");
    }
    void p_int_le_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_le_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print2var_reif(s,ce,ann,"<=");
    }
    void p_int_lt_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lt_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print2var_reif(s,ce,ann,"<");
    }

    void print_int_lin(FlatZincModel& s, const ConExpr& ce, AST::Node* ann, const std::string& op) {
        const auto& coeffs = ce[0]->getArray()->a;
        const auto& vars = ce[1]->getArray()->a;
        if (vars.size()!=coeffs.size())
            std::cerr << (*ce[0]) << " has not the same size as " << (*ce[1]) << std::endl;
        std::vector<unsigned int> uids;
        s.addOperator("*");
        s.addOperator("linear");
        s.addOperator(op);
        
        int rhs = ce[2]->getInt();
        for (unsigned int i = 0; i != vars.size(); ++i)
        {
            if (vars[i]->isInt()) /// wtf
            {
                rhs -= coeffs[i]->getInt() * vars[i]->getInt();
            }
            else
            {
                s.addInteger(coeffs[i]->getInt());
                unsigned int term = s.getNewTerm();
                std::cout << "9 3 " << term << " " << s.getOperatorUid("*") << " 2 " << s.getIntegerUid(coeffs[i]->getInt()) << " " << s.getIntVariableUid(vars[i]->getIntVar());
                uids.emplace_back(s.getNewElement());
                std::cout << "9 4 " << uids.back() << " 1 " << term << " 0\n";
                //std::cout << coeffs[i]->getInt() << " * i(" << s.iv[vars[i]->getIntVar()].getID() << ")";
                //if (i != vars.size()-1)
                //    std::cout << " + ";
            }
        } 
        s.addInteger(rhs);
        
        std::cout << "9 6 " << s.getTrueUid() << " " << s.getOperatorUid("linear") << " " << vars.size() << " ";
        for (const auto& uid : uids)
        {
            std::cout << uid << " ";
        }
        std::cout << s.getOperatorUid(op) << " " << s.getIntegerUid(rhs) << "\n";
    }
    
    
    void print_int_lin_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann, const std::string& op) {
        const auto& coeffs = ce[0]->getArray()->a;
        const auto& vars = ce[1]->getArray()->a;
        if (vars.size()!=coeffs.size())
            std::cerr << (*ce[0]) << " has not the same size as " << (*ce[1]) << std::endl;
        std::vector<unsigned int> uids;
        s.addOperator("*");
        s.addOperator("linear");
        s.addOperator(op);
        int rhs = ce[2]->getInt();
        
        for (unsigned int i = 0; i != vars.size(); ++i)
        {
            if (vars[i]->isInt()) /// wtf
            {
                rhs -= coeffs[i]->getInt() * vars[i]->getInt();
            }
            else
            {
                s.addInteger(coeffs[i]->getInt());
                unsigned int term = s.getNewTerm();
                std::cout << "9 3 " << term << " " << s.getOperatorUid("*") << " 2 " << s.getIntegerUid(coeffs[i]->getInt()) << " " << s.getIntVariableUid(vars[i]->getIntVar());
                uids.emplace_back(s.getNewElement());
                std::cout << "9 4 " << uids.back() << " 1 " << term << " 0\n";
                //std::cout << coeffs[i]->getInt() << " * i(" << s.iv[vars[i]->getIntVar()].getID() << ")";
                //if (i != vars.size()-1)
                //    std::cout << " + ";
            }
        } 
        
         s.addInteger(rhs);
        
        std::cout << "9 6 " << s.getBoolVariableUid(ce[3]->getBoolVar()) << " " << s.getOperatorUid("linear") << " " << vars.size() << " ";
        for (const auto& uid : uids)
        {
            std::cout << uid << " ";
        }
        std::cout << s.getOperatorUid(op) << " " << s.getIntegerUid(rhs) << "\n";
    }
    
    
    void p_int_lin_eq(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_eq("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print_int_lin(s,ce,ann,"=");
    }
    void p_int_lin_eq_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_eq_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<","<<(*ce[3])<<")::"<<(*ann)<<"\n";
      print_int_lin_reif(s,ce,ann,"=");
    }
    void p_int_lin_ne(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_ne("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print_int_lin(s,ce,ann,"!=");
    }
    void p_int_lin_ne_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_ne_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<","<<(*ce[3])<<")::"<<(*ann)<<"\n";
      print_int_lin_reif(s,ce,ann,"!=");
      
    }
    void p_int_lin_le(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_le("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print_int_lin(s,ce,ann,"<=");
    }
    void p_int_lin_le_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_le_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<","<<(*ce[3])<<")::"<<(*ann)<<"\n";
      print_int_lin_reif(s,ce,ann,"<=");
    }
    void p_int_lin_lt(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_lt("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print_int_lin(s,ce,ann,"<");
    }
    void p_int_lin_lt_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_lt_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<","<<(*ce[3])<<")::"<<(*ann)<<"\n";
      print_int_lin_reif(s,ce,ann,"<");
    }
    void p_int_lin_ge(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_ge("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print_int_lin(s,ce,ann,">=");
    }
    void p_int_lin_ge_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_ge_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<","<<(*ce[3])<<")::"<<(*ann)<<"\n";
      print_int_lin_reif(s,ce,ann,">=");
    }
    void p_int_lin_gt(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_gt("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      print_int_lin(s,ce,ann,">");
    }
    void p_int_lin_gt_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_lin_gt_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<","<<(*ce[3])<<")::"<<(*ann)<<"\n";
      print_int_lin_reif(s,ce,ann,">");
    }

    /* arithmetic constraints */
  
    void p_int_plus(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_plus("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
        s.addOperator("=");
        s.addOperator("linear");
        unsigned int elem1 = s.getNewElement();
        unsigned int id1;
        if (ce[0]->isInt())
            id1 = s.addInteger(ce[0]->getInt());
        else
            id1 = s.getIntVariableUid(ce[0]->getIntVar());
        unsigned int elem2 = s.getNewElement();
        unsigned int id2;
        if (ce[1]->isInt())
            id2 = s.addInteger(ce[1]->getInt());
        else
            id2 = s.getIntVariableUid(ce[1]->getIntVar());
        
        unsigned int id3;
        if (ce[2]->isInt())
            id3 = s.addInteger(ce[2]->getInt());
        else
            id3 = s.getIntVariableUid(ce[2]->getIntVar());
        std::cout << "9 4 " << elem1 << " 1 " << id1 << " 0\n";
        std::cout << "9 4 " << elem2 << " 1 " << id2 << " 0\n";
        std::cout << "9 6 " << s.getTrueUid() << " " << s.getOperatorUid("linear") << " ";
        std::cout << "2" << " " << elem1  << " " << elem2 << " " << s.getOperatorUid("=") << " " << id3 << "\n";        
        
    }

    void p_int_minus(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "int_minus("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
      s.addOperator("=");
      s.addOperator("*");
      s.addOperator("linear");
      s.addInteger(-1);
      
      unsigned int elem1 = s.getNewElement();
      unsigned int id1;
      if (ce[0]->isInt())
          id1 = s.addInteger(ce[0]->getInt());
      else
          id1 = s.getIntVariableUid(ce[0]->getIntVar());
      unsigned int elem2 = s.getNewElement();
      unsigned int id2;
      if (ce[1]->isInt())
          id2 = s.addInteger(ce[1]->getInt());
      else
          id2 = s.getIntVariableUid(ce[1]->getIntVar());
      
      unsigned int id3;
      if (ce[2]->isInt())
          id3 = s.addInteger(ce[2]->getInt());
      else
          id3 = s.getIntVariableUid(ce[2]->getIntVar());
      
      unsigned int term = s.getNewTerm();
      std::cout << "9 4 " << elem1 << " 1 " << id1 << " 0\n";
      std::cout << "9 3 " << term << " " << s.getOperatorUid("*") << " 2 " << s.getIntegerUid(-1) << " " << id2 << "\n";
      std::cout << "9 4 " << elem2 << " 1 " << term << " 0\n";
      std::cout << "9 6 " << s.getTrueUid() << " " << s.getOperatorUid("linear") << " ";
      std::cout << "2" << " " << elem1  << " " << elem2 << " " << s.getOperatorUid("=") << " " << id3 << "\n";        
    }

    void p_int_times(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "int_times("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
      throw AST::TypeError("non linear constraints not supported (multiplication)");
    }
    void p_int_div(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "int_div("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
      throw AST::TypeError("non linear constraints not supported (division)");
    }
    void p_int_mod(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "int_mod("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
      throw AST::TypeError("non linear constraints not supported (modulo)");
    }

    void p_int_min(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "int_min("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
      throw AST::TypeError("non linear constraints not supported (minimum)");
    }
    void p_int_max(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "int_max("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
      throw AST::TypeError("non linear constraints not supported (maximum)");
    }
    void p_int_negate(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "int_negate("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }

    void p_bool_eq(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
        //std::cerr << "bool_eq("<<(*ce[0])<<","<<(*ce[1])
        //  <<")::"<<(*ann)<<"\n";
        
        unsigned int id1;
        if (ce[0]->isBool())
        {
            if (ce[0]->getBool())
                id1 = s.getTrueUid();
            else
                id1 = s.getFalseUid();
        }
        else
            id1 = s.getBoolVariableUid(ce[0]->getBoolVar());
        unsigned int id2;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                id2 = s.getTrueUid();
            else
                id2 = s.getFalseUid();
        }
        else
            id2 = s.getBoolVariableUid(ce[1]->getBoolVar());
        
        std::cout << "1 1 0 0 2 " << id1 << " " << -id2 << "\n";
        std::cout << "1 1 0 0 2 " << -id1 << " " << id2 << "\n";
    }
    void p_bool_eq_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "bool_eq_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
        unsigned int id1;
        if (ce[0]->isBool())
        {
            if (ce[0]->getBool())
                id1 = s.getTrueUid();
            else
                id1 = s.getFalseUid();
        }
        else
            id1 = s.getBoolVariableUid(ce[0]->getBoolVar());
        unsigned int id2;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                id2 = s.getTrueUid();
            else
                id2 = s.getFalseUid();
        }
        else
            id2 = s.getBoolVariableUid(ce[1]->getBoolVar());
        
        unsigned int id3;
        if (ce[2]->isBool())
        {
            if (ce[2]->getBool())
                id3 = s.getTrueUid();
            else
                id3 = s.getFalseUid();
        }
        else
            id3 = s.getBoolVariableUid(ce[2]->getBoolVar());
        
      std::cout << "1 1 0 0 3 " << id1 << " " << -id2 << " " << id3 << "\n";
      std::cout << "1 1 0 0 3 " << -id1 << " " << id2 << " " << id3 << "\n";
      std::cout << "1 1 0 0 3 " << id1 << " " << id2 << " " << -id3 << "\n";
      std::cout << "1 1 0 0 3 " << -id1 << " " << -id2 << " " << -id3 << "\n";
    }
    void p_bool_ne(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "bool_ne("<<(*ce[0])<<","<<(*ce[1])
      //  <<")::"<<(*ann)<<"\n";
        unsigned int id1;
        if (ce[0]->isBool())
        {
            if (ce[0]->getBool())
                id1 = s.getTrueUid();
            else
                id1 = s.getFalseUid();
        }
        else
            id1 = s.getBoolVariableUid(ce[0]->getBoolVar());
        unsigned int id2;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                id2 = s.getTrueUid();
            else
                id2 = s.getFalseUid();
        }
        else
            id2 = s.getBoolVariableUid(ce[1]->getBoolVar());  
        
      std::cout << "1 1 0 0 2 " << id1 << " " << id2 << "\n";
      std::cout << "1 1 0 0 2 " << -id1 << " " << -id2 << "\n";
    }
    void p_bool_ne_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "bool_ne_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
        unsigned int id1;
        if (ce[0]->isBool())
        {
            if (ce[0]->getBool())
                id1 = s.getTrueUid();
            else
                id1 = s.getFalseUid();
        }
        else
            id1 = s.getBoolVariableUid(ce[0]->getBoolVar());
        unsigned int id2;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                id2 = s.getTrueUid();
            else
                id2 = s.getFalseUid();
        }
        else
            id2 = s.getBoolVariableUid(ce[1]->getBoolVar());
        
        unsigned int id3;
        if (ce[2]->isBool())
        {
            if (ce[2]->getBool())
                id3 = s.getTrueUid();
            else
                id3 = s.getFalseUid();
        }
        else
            id3 = s.getBoolVariableUid(ce[2]->getBoolVar());
        
      std::cout << "1 1 0 0 3 " << id1 << " " << id2 << " " << id3 << "\n";
      std::cout << "1 1 0 0 3 " << -id1 << " " << -id2 << " " << id3 << "\n";
      std::cout << "1 1 0 0 3 " << id1 << " " << -id2 << " " << -id3 << "\n";
      std::cout << "1 1 0 0 3 " << -id1 << " " << id2 << " " << -id3 << "\n";
    }
    }
    void p_bool_ge(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_ge("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_ge_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_ge_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_le(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_le("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_le_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_le_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_gt(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_gt("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_gt_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_gt_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_lt(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_lt("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_lt_reif(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_lt_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }

    void p_bool_or(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "bool_or("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
        unsigned int id1;
        if (ce[0]->isBool())
        {
            if (ce[0]->getBool())
                id1 = s.getTrueUid();
            else
                id1 = s.getFalseUid();
        }
        else
            id1 = s.getBoolVariableUid(ce[0]->getBoolVar());
        unsigned int id2;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                id2 = s.getTrueUid();
            else
                id2 = s.getFalseUid();
        }
        else
            id2 = s.getBoolVariableUid(ce[1]->getBoolVar());
        
        unsigned int id3;
        if (ce[2]->isBool())
        {
            if (ce[2]->getBool())
                id3 = s.getTrueUid();
            else
                id3 = s.getFalseUid();
        }
        else
            id3 = s.getBoolVariableUid(ce[2]->getBoolVar());
      std::cout << "1 1 0 0 2 " << id1 << " " << -id3 << "\n";
      std::cout << "1 1 0 0 2 " << id2 << " " << -id3 << "\n";
      std::cout << "1 1 0 0 3 " << -id1 << " "<< -id2 << " " << id3 << "\n";
    }
    void p_bool_and(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "bool_and("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
        unsigned int id1;
        if (ce[0]->isBool())
        {
            if (ce[0]->getBool())
                id1 = s.getTrueUid();
            else
                id1 = s.getFalseUid();
        }
        else
            id1 = s.getBoolVariableUid(ce[0]->getBoolVar());
        unsigned int id2;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                id2 = s.getTrueUid();
            else
                id2 = s.getFalseUid();
        }
        else
            id2 = s.getBoolVariableUid(ce[1]->getBoolVar());
        
        unsigned int id3;
        if (ce[2]->isBool())
        {
            if (ce[2]->getBool())
                id3 = s.getTrueUid();
            else
                id3 = s.getFalseUid();
        }
        else
            id3 = s.getBoolVariableUid(ce[2]->getBoolVar());
      std::cout << "1 1 0 0 3 " << id1 << " " << id2 << " " << -id3 << "\n";
      std::cout << "1 1 0 0 2 " << -id1 << " " << id3 << "\n";
      std::cout << "1 1 0 0 2 " << -id2 << " " << id3 << "\n";
    }
    void p_array_bool_and(FlatZincModel& s, const ConExpr& ce, AST::Node* ann)
    {
      //std::cerr << "array_bool_and("<<(*ce[0])<<","<<(*ce[1])
      //  <<")::"<<(*ann)<<"\n";
                
        unsigned int idreif;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                idreif = s.getTrueUid();
            else
                idreif = s.getFalseUid();
        }
        else
            idreif = s.getBoolVariableUid(ce[0]->getBoolVar());
        
        std::cout << "1 1 0 0 " << ce[0]->getArray()->a.size()+1 << " ";
        for (const auto& i : ce[0]->getArray()->a)
        {
            if (i->isBool())
            {
                if (i->getBool())
                    std::cout << s.getTrueUid() << " ";
                else
                    std::cout << s.getFalseUid() << " ";
            }
            else
                std::cout << s.getBoolVariableUid(i->getBoolVar()) << " ";
        }
        std::cout << -idreif << "\n";
        for (const auto& i : ce[0]->getArray()->a)
        {
            if (i->isBool())
            {
                if (i->getBool())
                    std::cout << "1 1 0 0 2" << s.getFalseUid() << " " << idreif << "\n";
                else
                    std::cout << "1 1 0 0 2" << s.getTrueUid() << " " << idreif << "\n";
            }
            else
                std::cout << "1 1 0 0 2" << -s.getBoolVariableUid(i->getBoolVar()) << " " << idreif << "\n";
        }
    }
    void p_array_bool_or(FlatZincModel& s, const ConExpr& ce, AST::Node* ann)
    {
        unsigned int idreif;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                idreif = s.getTrueUid();
            else
                idreif = s.getFalseUid();
        }
        else
            idreif = s.getBoolVariableUid(ce[0]->getBoolVar());
      //std::cerr << "array_bool_or("<<(*ce[0])<<","<<(*ce[1])
      //  <<")::"<<(*ann)<<"\n";
      for (const auto& i : ce[0]->getArray()->a)
      {
          if (i->isBool())
          {
              if (i->getBool())
                  std::cout << "1 1 0 0 2" << s.getTrueUid() << " " << -idreif << "\n";
              else
                  std::cout << "1 1 0 0 2" << s.getFalseUid() << " " << -idreif << "\n";
          }
          else
            std::cout << "1 1 0 0 2 " << s.getBoolVariableUid(i->getBoolVar()) << " " << -idreif << "\n";
      }
      std::cout << "1 1 0 0 " << ce[0]->getArray()->a.size()+1 << " ";
      for (const auto& i : ce[0]->getArray()->a)
      {
          if (i->isBool())
          {
              if (i->getBool())
                  std::cout << s.getFalseUid() << " ";
              else
                  std::cout << s.getTrueUid() << " ";
          }
          else
            std::cout << -s.getBoolVariableUid(i->getBoolVar()) << " ";
      }
      std::cout << idreif << "\n";
    }
    void p_array_bool_clause(FlatZincModel& s, const ConExpr& ce,
                             AST::Node* ann) {
      //std::cerr << "array_bool_clause("<<(*ce[0])<<","<<(*ce[1])
      //  <<")::"<<(*ann)<<"\n";
      // can also have boolLits, which is true/false
      for (const auto& i : ce[0]->getArray()->a)
          if (i->isBool() && i->getBool()==true)
              return;
      for (const auto& i : ce[1]->getArray()->a)
          if (i->isBool() && i->getBool()==false)
              return; 
      std::cout << "1 1 0 0 " << ce[0]->getArray()->a.size()+ ce[1]->getArray()->a.size() << " ";
      for (const auto& i : ce[0]->getArray()->a)
          if (!i->isBool())
            std::cout << -s.getBoolVariableUid(i->getBoolVar()) << " ";
      for (const auto& i : ce[1]->getArray()->a)
          if (!i->isBool())
            std::cout << s.getBoolVariableUid(i->getBoolVar()) << " ";
      std::cout << "\n";
    }
    void p_array_bool_clause_reif(FlatZincModel& s, const ConExpr& ce,
                             AST::Node* ann) {
      std::cerr << "array_bool_clause_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_xor(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "bool_xor("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
      //  <<")::"<<(*ann)<<"\n";
        unsigned int id1;
        if (ce[0]->isBool())
        {
            if (ce[0]->getBool())
                id1 = s.getTrueUid();
            else
                id1 = s.getFalseUid();
        }
        else
            id1 = s.getBoolVariableUid(ce[0]->getBoolVar());
        unsigned int id2;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                id2 = s.getTrueUid();
            else
                id2 = s.getFalseUid();
        }
        else
            id2 = s.getBoolVariableUid(ce[1]->getBoolVar());
        
        unsigned int id3;
        if (ce[2]->isBool())
        {
            if (ce[2]->getBool())
                id3 = s.getTrueUid();
            else
                id3 = s.getFalseUid();
        }
        else
            id3 = s.getBoolVariableUid(ce[2]->getBoolVar());
      std::cout << "1 1 0 0 3 " << id1 << " "<< -id2 << " " << -id3 << "\n";
      std::cout << "1 1 0 0 3 " << -id1 << " "<< id2 << " " << -id3 << "\n";
      std::cout << "1 1 0 0 3 " << id1 << " "<< id2 << " " << id3 << "\n";
      std::cout << "1 1 0 0 3 " << -id1 << " "<< -id2 << " " << id3 << "\n";
    }
    void p_bool_l_imp(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_l_imp("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_r_imp(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "bool_r_imp("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_bool_not(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "bool_not("<<(*ce[0])<<","<<(*ce[1])
      //  <<")::"<<(*ann)<<"\n";
        unsigned int id1;
        if (ce[0]->isBool())
        {
            if (ce[0]->getBool())
                id1 = s.getTrueUid();
            else
                id1 = s.getFalseUid();
        }
        else
            id1 = s.getBoolVariableUid(ce[0]->getBoolVar());
        unsigned int id2;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                id2 = s.getTrueUid();
            else
                id2 = s.getFalseUid();
        }
        else
            id2 = s.getBoolVariableUid(ce[1]->getBoolVar());
        
      std::cout << "1 1 0 0 2 " << -id1 << " " << -id2 << "\n";
      std::cout << "1 1 0 0 2 " << id1 << " " << id2 << "\n";
    }
  
    /* element constraints */
    void p_array_int_element(FlatZincModel& s, const ConExpr& ce, 
                                 AST::Node* ann) {
      std::cerr << "array_int_element("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_array_bool_element(FlatZincModel& s, const ConExpr& ce, 
                                  AST::Node* ann) {
      std::cerr << "array_bool_element("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
  
    /* coercion constraints */
    void p_bool2int(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      //std::cerr << "bool2int("<<(*ce[0])<<","<<(*ce[1])
      //  <<")::"<<(*ann)<<"\n";

        s.addOperator("=");
        
        s.addInteger(1);
        s.addOperator("linear");
        /// create reification for x=1
        unsigned int elem = s.getNewElement();
        std::cout << "9 4 " << elem << " 1 " << s.getIntVariableUid(ce[1]->getIntVar()) << " 0\n";
        std::cout << "9 6 " << s.getBoolVariableUid(ce[0]->getBoolVar()) << " " << s.getOperatorUid("linear") << "  1 " << elem << " " << s.getOperatorUid("=") << " " << s.getIntegerUid(1) << "\n";
        
        const IntVar& x = s.iv[ce[1]->getIntVar()];
        const auto& dom = x.getDomain();
        if ( (dom->interval && dom->min==0 && dom->max==1) || (dom->s.size()==2 && ((dom->s[0]==0 && dom->s[1]==1) || (dom->s[1]==0 && dom->s[0]==1))))
        {}
        else
        {
            
            //UNSAT !!!, if x > 1 this is not allowed, so post
            //        true <=> x<=1 and x>=0
            s.addOperator("<=");
            s.addOperator("linear");
            s.addInteger(1);
            unsigned int elem1 = s.getNewElement();
            std::cout << "9 4 " << elem << " 1 " << s.getIntVariableUid(ce[1]->getIntVar()) << " 0\n";
            std::cout << "9 6 " << s.getTrueUid() << " " << s.getOperatorUid("linear") << " ";
            std::cout << "1" << " " << elem1 << " " << s.getOperatorUid("<=") << " " << s.getIntVariableUid(1) << "\n";   
            
            s.addOperator(">=");
            s.addInteger(0);

            std::cout << "9 6 " << s.getTrueUid() << " " << s.getOperatorUid("linear") << " ";
            std::cout << "1" << " " << elem << " " << s.getOperatorUid(">=") << " " << s.getIntVariableUid(0) << "\n";
         }
    }

    void p_int_in(FlatZincModel& s, const ConExpr& ce, AST::Node *ann) {
      //std::cerr << "int_in("<<(*ce[0])<<","<<(*ce[1])
      //  <<")::"<<(*ann)<<"\n";
        
      //std::cout << "TODOAssert if domain is different from definition domain(i(" << s.iv[ce[0]->getIntVar()].getID() << "), ";
//      AST::SetLit* p = ce[1]->getSet();
//      if (p->interval)
//      {
//          const auto dom = s.iv[ce[0]->getIntVar()].getDomain();
//          if (!dom->interval || p->min!=dom->min || p->max!=dom->max)
//              throw AST::TypeError("Interval seems to have changed, internal error");
//          //std::cout << p->min << ".." << p->max;
//      }
//      else
//      {
//          const auto dom = s.iv[ce[0]->getIntVar()].getDomain();
//          if (dom->interval || dom->s != p->s)
//              throw AST::TypeError("Interval seems to have changed, internal error");
////          for (unsigned int i = 0; i < p->s.size()-1; ++i)
////              std::cout << p->s[i] << ",";
////          std::cout << p->s.back();
//      }
      //std::cout << ").\n";
    }
    
    /// accepts an array of integer variables
    void myalldiff(FlatZincModel& s, const ConExpr& ce, AST::Node *ann) {
        
        s.addOperator("distinct");
        const auto& a = ce[0]->getArray()->a;
        std::vector<unsigned int> elems;
        for (const auto& i :a)
        {
            elems.emplace_back(s.getNewElement());
            std::cout << "9 4 " << elems.back() << " 1 " << s.getIntVariableUid(i->getIntVar()) << " 0\n";
        }
        std::cout << "9 5 " << s.getTrueUid() << " " << s.getOperatorUid("distinct") << " " << elems.size() << " ";
        for (const auto& i :elems)
            std::cout << i << " ";
        std::cout << "\n";         
    }
    
    /// accepts an array of integer variables, and a boolean variable
    void myalldiff_reif(FlatZincModel& s, const ConExpr& ce, AST::Node *ann) {
        
        s.addOperator("distinct");
        const auto& a = ce[0]->getArray()->a;
        std::vector<unsigned int> elems;
        for (const auto& i :a)
        {
            elems.emplace_back(s.getNewElement());
            unsigned int id;
            if (i->isInt())
            {
                id = s.addInteger(i->getInt());
            }
            else
                id = s.getIntVariableUid(i->getIntVar());
            std::cout << "9 4 " << elems.back() << " 1 " << id << " 0\n";
        }
        unsigned int idreif;
        if (ce[1]->isBool())
        {
            if (ce[1]->getBool())
                idreif = s.getTrueUid();
            else
                idreif = s.getFalseUid();
        }
        else
            idreif = s.getBoolVariableUid(ce[1]->getBoolVar());
        std::cout << "9 5 " << idreif << " " << s.getOperatorUid("distinct") << " " << elems.size() << " ";
        for (const auto& i :elems)
            std::cout << i << " ";
        std::cout << "\n";         
    }

    void p_abs(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "abs("<<(*ce[0])<<","<<(*ce[1])<<")::"<<(*ann)<<"\n";
    }

    class IntPoster {
    public:
      IntPoster(void) {
        registry().add("int_eq", &p_int_eq);
        registry().add("int_ne", &p_int_ne);
        registry().add("int_ge", &p_int_ge);
        registry().add("int_gt", &p_int_gt);
        registry().add("int_le", &p_int_le);
        registry().add("int_lt", &p_int_lt);
        registry().add("int_eq_reif", &p_int_eq_reif);
        registry().add("int_ne_reif", &p_int_ne_reif);
        registry().add("int_ge_reif", &p_int_ge_reif);
        registry().add("int_gt_reif", &p_int_gt_reif);
        registry().add("int_le_reif", &p_int_le_reif);
        registry().add("int_lt_reif", &p_int_lt_reif);
        registry().add("int_lin_eq", &p_int_lin_eq);
        registry().add("int_lin_eq_reif", &p_int_lin_eq_reif);
        registry().add("int_lin_ne", &p_int_lin_ne);
        registry().add("int_lin_ne_reif", &p_int_lin_ne_reif);
        registry().add("int_lin_le", &p_int_lin_le);
        registry().add("int_lin_le_reif", &p_int_lin_le_reif);
        registry().add("int_lin_lt", &p_int_lin_lt);
        registry().add("int_lin_lt_reif", &p_int_lin_lt_reif);
        registry().add("int_lin_ge", &p_int_lin_ge);
        registry().add("int_lin_ge_reif", &p_int_lin_ge_reif);
        registry().add("int_lin_gt", &p_int_lin_gt);
        registry().add("int_lin_gt_reif", &p_int_lin_gt_reif);
        registry().add("int_plus", &p_int_plus);
        registry().add("int_minus", &p_int_minus);
        registry().add("int_times", &p_int_times);
        registry().add("int_div", &p_int_div);
        registry().add("int_mod", &p_int_mod);
        registry().add("int_min", &p_int_min);
        registry().add("int_max", &p_int_max);
        registry().add("int_abs", &p_abs);
        registry().add("int_negate", &p_int_negate);
        registry().add("bool_eq", &p_bool_eq);
        registry().add("bool_eq_reif", &p_bool_eq_reif);
        registry().add("bool_ne", &p_bool_ne);
        registry().add("bool_ne_reif", &p_bool_ne_reif);
        registry().add("bool_ge", &p_bool_ge);
        registry().add("bool_ge_reif", &p_bool_ge_reif);
        registry().add("bool_le", &p_bool_le);
        registry().add("bool_le_reif", &p_bool_le_reif);
        registry().add("bool_gt", &p_bool_gt);
        registry().add("bool_gt_reif", &p_bool_gt_reif);
        registry().add("bool_lt", &p_bool_lt);
        registry().add("bool_lt_reif", &p_bool_lt_reif);
        registry().add("bool_or", &p_bool_or);
        registry().add("bool_and", &p_bool_and);
        registry().add("bool_xor", &p_bool_xor);
        registry().add("array_bool_and", &p_array_bool_and);
        registry().add("array_bool_or", &p_array_bool_or);
        registry().add("bool_clause", &p_array_bool_clause);
        registry().add("bool_clause_reif", &p_array_bool_clause_reif);
        registry().add("bool_left_imp", &p_bool_l_imp);
        registry().add("bool_right_imp", &p_bool_r_imp);
        registry().add("bool_not", &p_bool_not);
        registry().add("array_int_element", &p_array_int_element);
        registry().add("array_var_int_element", &p_array_int_element);
        registry().add("array_bool_element", &p_array_bool_element);
        registry().add("array_var_bool_element", &p_array_bool_element);
        registry().add("bool2int", &p_bool2int);
        registry().add("int_in", &p_int_in);
        registry().add("all_different_int", &myalldiff);
        registry().add("all_different_intreif", &myalldiff_reif);

      }
    };
    IntPoster __int_poster;

    void p_set_union(FlatZincModel& s, const ConExpr& ce, AST::Node *ann) {
      std::cerr << "set_union("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_intersect(FlatZincModel& s, const ConExpr& ce, AST::Node *ann) {
      std::cerr << "set_intersect("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_diff(FlatZincModel& s, const ConExpr& ce, AST::Node *ann) {
      std::cerr << "set_diff("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }

    void p_set_symdiff(FlatZincModel& s, const ConExpr& ce, AST::Node* ann) {
      std::cerr << "set_symdiff("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }

    void p_set_eq(FlatZincModel& s, const ConExpr& ce, AST::Node * ann) {
      std::cerr << "set_eq("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_ne(FlatZincModel& s, const ConExpr& ce, AST::Node * ann) {
      std::cerr << "set_ne("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_subset(FlatZincModel& s, const ConExpr& ce, AST::Node * ann) {
      std::cerr << "set_subset("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_superset(FlatZincModel& s, const ConExpr& ce, AST::Node * ann) {
      std::cerr << "set_superset("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_card(FlatZincModel& s, const ConExpr& ce, AST::Node * ann) {
      std::cerr << "set_card("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_in(FlatZincModel& s, const ConExpr& ce, AST::Node * ann) {
      std::cerr << "set_in("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_eq_reif(FlatZincModel& s, const ConExpr& ce, AST::Node * ann) {
      std::cerr << "set_eq_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_ne_reif(FlatZincModel& s, const ConExpr& ce, AST::Node * ann) {
      std::cerr << "set_ne_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_subset_reif(FlatZincModel& s, const ConExpr& ce,
                           AST::Node *ann) {
      std::cerr << "set_subset_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_superset_reif(FlatZincModel& s, const ConExpr& ce,
                             AST::Node *ann) {
      std::cerr << "set_superset_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_in_reif(FlatZincModel& s, const ConExpr& ce, AST::Node *ann) {
      std::cerr << "set_in_reif("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }
    void p_set_disjoint(FlatZincModel& s, const ConExpr& ce, AST::Node *ann) {
      std::cerr << "set_disjoint("<<(*ce[0])<<","<<(*ce[1])
        <<")::"<<(*ann)<<"\n";
    }

    void p_array_set_element(FlatZincModel& s, const ConExpr& ce,
                             AST::Node* ann) {
      std::cerr << "array_set_element("<<(*ce[0])<<","<<(*ce[1])<<","<<(*ce[2])
        <<")::"<<(*ann)<<"\n";
    }


    class SetPoster {
    public:
      SetPoster(void) {
        registry().add("set_eq", &p_set_eq);
        registry().add("set_ne", &p_set_ne);
        registry().add("set_union", &p_set_union);
        registry().add("array_set_element", &p_array_set_element);
        registry().add("array_var_set_element", &p_array_set_element);
        registry().add("set_intersect", &p_set_intersect);
        registry().add("set_diff", &p_set_diff);
        registry().add("set_symdiff", &p_set_symdiff);
        registry().add("set_subset", &p_set_subset);
        registry().add("set_superset", &p_set_superset);
        registry().add("set_card", &p_set_card);
        registry().add("set_in", &p_set_in);
        registry().add("set_eq_reif", &p_set_eq_reif);
        registry().add("equal_reif", &p_set_eq_reif);
        registry().add("set_ne_reif", &p_set_ne_reif);
        registry().add("set_subset_reif", &p_set_subset_reif);
        registry().add("set_superset_reif", &p_set_superset_reif);
        registry().add("set_in_reif", &p_set_in_reif);
        registry().add("disjoint", &p_set_disjoint);
      }
    };
    SetPoster __set_poster;
}

// STATISTICS: flatzinc-any
