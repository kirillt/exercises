#include <iostream>
#include <functional>
 
#include <utility>
#include <list>
 
using namespace std;
 
// higher-order funtions
 
template <typename Domain, typename Codomain>
list<Codomain> map(function<Codomain (Domain)> f, list<Domain> xs) {
    list<Codomain> mapped;
    for (const Domain x : xs) {
        mapped.push_back(f(x));
    }
    return mapped;
}
 
template <typename Codomain, typename First, typename Second, typename Third>
function<Codomain (Second,Third)> apply3(function<Codomain (First, Second,Third)> f, First first) {
    auto applied = [f,first](Second second, Third third) -> Codomain {
        return f(first,second,third);
    };
    return applied;
}
 
template <typename Codomain, typename First, typename Second>
function<Codomain (pair<First,Second>)> uncurry(function<Codomain (First,Second)> f) {
    auto curried = [f](pair<First,Second> p) -> Codomain {
        return f(p.first,p.second);
    };
    return curried;
}
 
// solution
 
double integral(function<double (double)> f, double l, double r) {
   static const double resolution = 0.0001;
   if (l > r) {
       double x = l;
       l = r; r = l;
   }
   
   const double range = r - l;
   const double step  = range * resolution;
   
   double result = 0;
   for (double x = l; x <= r - step; x += step) {
       result += f(x) * step;
   }
   return result;
}

bool print(double x) {
    cout << x << endl;
    return true;
}
 
int main()
{
    typedef pair<double,double> bounds;
    #define functiond function<double (double)>
    #define uncurryd  uncurry<double,double,double>
    #define apply3d   apply3<double,functiond,double,double>
    #define mapd_     map<double,bool>

    auto f = [](double x) -> double {
        return x*x;
    };

    list<bounds> xs = {{1,2},{3,4},{5,6}};
    list<double> ys = map(uncurryd(apply3d(integral, f)), xs);
    mapd_(print, ys);
}
