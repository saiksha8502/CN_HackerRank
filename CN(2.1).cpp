#define _CRT_SECURE_NO_WARNINGS
#include <string>
#include <vector>
#include <algorithm>
#include <numeric>
#include <set>
#include <map>
#include <queue>
#include <iostream>
#include <sstream>
#include <cstdio>
#include <cmath>
#include <ctime>
#include <cstring>
#include <cctype>
#include <cassert>
#include <limits>
#include <functional>
#include <bitset>
#define rep(i,n) for(int (i)=0;(i)<(int)(n);++(i))
#define rer(i,l,u) for(int (i)=(int)(l);(i)<=(int)(u);++(i))
#define reu(i,l,u) for(int (i)=(int)(l);(i)<(int)(u);++(i))
#if defined(_MSC_VER) || __cplusplus > 199711L
#define aut(r,v) auto r = (v)
#else
#define aut(r,v) typeof(v) r = (v)
#endif
#define each(it,o) for(aut(it, (o).begin()); it != (o).end(); ++ it)
#define all(o) (o).begin(), (o).end()
#define pb(x) push_back(x)
#define mp(x,y) make_pair((x),(y))
#define mset(m,v) memset(m,v,sizeof(m))
#define INF 0x3f3f3f3f
#define INFL 0x3f3f3f3f3f3f3f3fLL
using namespace std;
typedef vector<int> vi; typedef pair<int,int> pii; 
typedef vector<pair<int,int> > vpii;
typedef long long ll; typedef vector<long long> vl; 
typedef pair<long long,long long> pll; 
typedef vector<pair<long long,long long> > vpll;
typedef vector<string> vs; 
typedef long double ld;
template<typename T, typename U> inline void amin(T &x, U y) { if(y < x) x = y; }
template<typename T, typename U> inline void amax(T &x, U y) { if(x < y) x = y; }


unsigned xor128() {
static unsigned x = 123456789, y = 362436069, z = 521288629, w = 88675123;
unsigned t = x ^ (x << 11);
x = y; y = z; z = w;
return w = w ^ (w >> 19) ^ (t ^ (t >> 8));
}

template<typename Derived>
struct PNodeBase {
Derived *left, *right, *parent;
int size;
PNodeBase(): left(NULL), right(NULL), parent(NULL), size(1) { }
inline Derived *update() {
size = (!left ? 0 : left->size) + 1 + (!right ? 0 : right->size);
return derived();
}
inline void propagate() { }
inline Derived *linkl(Derived *c) {
if(left = c) c->parent = derived();
return derived()->update();
}
inline Derived *linkr(Derived *c) {
if(right = c) c->parent = derived();
return derived()->update();
}
inline Derived *linklr(Derived *l, Derived *r) {
if(left = l) l->parent = derived();
if(right = r) r->parent = derived();
return derived()->update();
}
static inline Derived *cut(Derived *t) {
if(t) t->parent = NULL;
return t;
}
private:
inline Derived *derived() 
{ return static_cast<Derived*>(this); }
};
struct Node : PNodeBase<Node> {
typedef PNodeBase<Node> Base;
int weight, sum;
bool reversed;
Node(): weight(0), sum(0), reversed(false) { }
Node *update() {
sum = (!left ? 0 : left->sum) + weight + (!right ? 0 : right->sum);
return static_cast<Base*>(this)->update();
}
inline void propagate() {
if(reversed) {
swap(left, right);
if(left != 0) left->reversed ^= true;
if(right != 0) right->reversed ^= true;
reversed = false;
}
return static_cast<Base*>(this)->propagate();
}
};

struct PRBSTBase {
typedef Node *Ref;
static int size(Ref t) { return !t ? 0 : t->size; }
static Ref join(Ref l, Ref r) {
if(!l) return r;
if(!r) return l;
if((int)(xor128() % (l->size + r->size)) < l->size) {
l->propagate();
return l->linkr(join(Node::cut(l->right), r));
}else {
r->propagate();
return r->linkl(join(l, Node::cut(r->left)));
}
}
typedef pair<Ref,Ref> RefPair;
static RefPair split(Ref t, int k) {
if(!t) return RefPair((Ref)NULL, (Ref)NULL);
t->propagate();
int s = size(t->left);
if(k <= s) {
RefPair p = split(Node::cut(t->left), k);
return RefPair(p.first, t->linkl(p.second));
}else {
RefPair p = split(Node::cut(t->right), k - s - 1);
return RefPair(t->linkr(p.first), p.second);
}
}
static Ref insert(Ref t, int k, Ref n) {
if(!t) return n;
if(xor128() % (t->size + 1) == 0) {
RefPair p = split(t, k);
return n->linklr(p.first, p.second);
}
t->propagate();
int s = size(t->left);
if(k <= s)
return t->linkl(insert(Node::cut(t->left), k, n));
else
return t->linkr(insert(Node::cut(t->right), k - s - 1, n));
}
static RefPair remove(Ref t, int k) {
if(!t) return RefPair((Ref)NULL, (Ref)NULL);
t->propagate();
int s = size(t->left);
if(k < s) {
RefPair p = remove(Node::cut(t->left), k);
return RefPair(t->linkl(p.first), p.second);
}else if(k > s) {
RefPair p = remove(Node::cut(t->right), k - s - 1);
return RefPair(t->linkr(p.first), p.second);
}else {
Ref a = join(Node::cut(t->left), Node::cut(t->right));
return RefPair(a, t->linklr(NULL, NULL));
}
}
static Ref index(Ref t, int k) {
if(!t) return NULL;
t->propagate();
int s = size(t->left);
if(k < s)
return index(t->left, k);
else if(k > s)
return index(t->right, k - s - 1);
else
return t;
}
static void topDown(Ref t) {
Ref nodes[128]; int k = 0;
for(Ref u = t; u != 0; u = u->parent)
nodes[k ++] = u;
while(k > 0)
nodes[-- k]->propagate();
}
static pair<Ref,int> findRoot(Ref t) {
if(!t) return make_pair((Ref)NULL, 0);
topDown(t);
int k = size(t->left);
while(true) {
Ref p = t->parent;
if(!p) return make_pair(t, k);
if(p->right == t)
k += size(p->left) + 1;
t = p;
}
}
};
typedef PRBSTBase BST;

struct Vector2 {
int a[2], s;
Vector2(): s(0) { }
int operator[](int i) const { assert(i < s); return a[i]; }
void push_back(int x) { a[s ++] = x; }
void erase(int x) { s = remove(a, a + s, x) - a; }
int size() const { return s; }
bool empty() const { return s == 0; }
};

void link(int i, int a, int x, int y, 
const vector<vector<Vector2> > &g, vector<Node> &nodes) {
Node *t = &nodes[i];
assert(BST::size(t) == 1);
if(!g[a][x].empty()) {
Node *l = &nodes[g[a][x][0]];
pair<Node*,int> pl = BST::findRoot(l);
if(pl.second != BST::size(pl.first) - 1) {
assert(pl.second == 0);
pl.first->reversed ^= true;
}
t = BST::join(pl.first, t);
}
if(!g[a][y].empty()) {
Node *r = &nodes[g[a][y][0]];
pair<Node*,int> pr = BST::findRoot(r);
if(pr.second != 0) {
assert(pr.second == BST::size(pr.first) - 1);
pr.first->reversed ^= true;
}
t = BST::join(t, pr.first);
}
}

int main() {
int S, L, AA, T;
scanf("%d%d%d%d", &S, &L, &AA, &T);
vector<vector<Vector2> > g(AA, vector<Vector2>(S));
map<pii,int> links;
vector<pii> edges(L);
vector<Node> nodes(L);
vector<int> admin(L, -1);
rep(i, L) {
int x, y, a;
scanf("%d%d%d", &x, &y, &a), -- x, -- y, -- a;
if(x > y) swap(x, y);

link(i, a, x, y, g, nodes);

g[a][x].push_back(i);
g[a][y].push_back(i);

edges[i] = mp(x, y);
links[mp(x, y)] = i;
admin[i] = a;
}
const char *msgs[9] = {
"?????\n",
"Wrong link\n",
"Already controlled link\n",
"Server overload\n",
"Network redundancy\n",
"Assignment done\n",
"",
"No connection\n",
"%d security devices placed\n",
};
rep(ii, T) {
int ty, A, B, x, a;
scanf("%d%d%d%d", &ty, &A, &B, &x), -- A, -- B;
a = x - 1;
if(A > B) swap(A, B);

int result; int ans = -1;
if(ty == 1) {
auto it = links.find(mp(A, B));
if(it == links.end()) {
result = 1;
}else if(admin[it->second] == a) {
result = 2;
}else if(g[a][A].size() >= 2 || g[a][B].size() >= 2) {
result = 3;
}else {
int i = it->second, pa = admin[i];
Node *tt = &nodes[i];
pair<Node*,int> p = BST::findRoot(tt);
Node *t = p.first;

{
Node *l = g[a][A].empty() ? 0 :
 BST::findRoot(&nodes[g[a][A][0]]).first;
Node *r = g[a][B].empty() ? 0 : 
BST::findRoot(&nodes[g[a][B][0]]).first;
if(l != 0 && r != 0 && l == r) {
result = 4;
goto next;
}
}

//??admin?????????
if(p.second != 0) {
int j = BST::index(p.first, p.second - 1) - &nodes[0];
if(admin[j] == pa) {
p.first = BST::split(p.first, p.second).second;
p.second = 0;
}
}
if(p.second != BST::size(p.first) - 1) {
int j = BST::index(p.first, p.second + 1) - &nodes[0];
if(admin[j] == pa) {
p.first = BST::split(p.first, p.second + 1).first;
}
}
g[pa][A].erase(i);
g[pa][B].erase(i);

link(i, a, A, B, g, nodes);

g[a][A].push_back(i);
g[a][B].push_back(i);

admin[i] = a;

result = 5;
}
}else if(ty == 2) {
if(!links.count(mp(A, B))) abort();
int i = links[mp(A, B)];
Node *tt = &nodes[i];
pair<Node*,int> p = BST::findRoot(tt);
Node *u = BST::remove(p.first, p.second).first;
tt->weight = x;
tt->update();
BST::insert(u, p.second, tt);
result = 6;
}else if(ty == 3) {
if(A == B) {
result = 8, ans = 0;
goto next;
}
if(g[a][A].empty() || g[a][B].empty()) {
result = 7;
goto next;
}
Node *l = &nodes[g[a][A][0]];
Node *r = &nodes[g[a][B][0]];
pair<Node*,int> pl = BST::findRoot(l);
pair<Node*,int> pr = BST::findRoot(r);
if(pl.first != pr.first) {
result = 7;
goto next;
}
if(g[a][A].size() == 2) {
Node *l1 = &nodes[g[a][A][1]];
pair<Node*,int> pl1 = BST::findRoot(l1);
if(pl1.first != pl.first) abort();
if(abs(pl.second - pr.second) > abs(
    pl1.second - pr.second))
l = l1, pl = pl1;
}
if(g[a][B].size() == 2) {
Node *r1 = &nodes[g[a][B][1]];
pair<Node*,int> pr1 = BST::findRoot(r1);
if(pr1.first != pr.first) abort();
if(abs(pl.second - pr.second) > abs(
    
    pl.second - pr1.second))
r = r1, pr = pr1;
}
Node *t = pl.first;
int L = pl.second, R = pr.second;
if(L > R) swap(L, R);
pair<Node*,Node*> p = BST::split(t, R + 1);
pair<Node*,Node*> q = BST::split(p.first, L);

Node *u = q.second;
result = 8;
ans = u->sum;

t = BST::join(BST::join(q.first, q.second), p.second);
}
next:;
printf(msgs[result], ans);
}
return 0;
}