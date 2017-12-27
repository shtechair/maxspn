package maxspn

import (
	"bytes"
	"io/ioutil"
	"log"
	"math"
	"strconv"
)

var ( // Main API
	_ = LoadSPN
	_ = MAP2MAX
)

type Node interface {
	ID() int
	SetID(id int)
}

type SPN struct {
	Nodes  []Node
	Schema []int
}
type SumEdge struct {
	Weight float64 // in log domain
	Node   Node
}

type PrdEdge struct {
	Node Node
}
type Trm struct {
	Kth   int // k-th variable
	Value int // variable state
	id    int
}
type Sum struct {
	Edges []SumEdge
	id    int
}

type Prd struct {
	Edges []PrdEdge
	id    int
}

func (t *Trm) ID() int      { return t.id }
func (t *Trm) SetID(id int) { t.id = id }
func (s *Sum) ID() int      { return s.id }
func (s *Sum) SetID(id int) { s.id = id }
func (p *Prd) ID() int      { return p.id }

func (p *Prd) SetID(id int) { p.id = id }

func LoadSPN(filename string) SPN {
	bs, err := ioutil.ReadFile(filename)
	if err != nil {
		log.Fatal(err)
	}
	bss := bytes.Split(bs, []byte("\n"))
	end := len(bss) - 1
	for string(bss[end]) != "EOF" {
		end--
	}

	scs := bytes.Split(bss[0][1:len(bss[0])-1], []byte(" "))
	schema := make([]int, len(scs))
	for i, s := range scs {
		schema[i] = parseInt(string(s))
	}

	bss = bss[1:end]
	nodes := make([]Node, len(bss))
	for i, ln := range bss {
		bs := bytes.Split(ln, []byte(" "))
		switch string(bs[0]) {
		case "v":
			nodes[i] = &Trm{
				Kth:   parseInt(string(bs[1])),
				Value: parseInt(string(bs[2])),
				id:    i,
			}
		case "+":
			es := make([]SumEdge, len(bs)/2)
			for j := 1; j < len(bs); j += 2 {
				node := nodes[parseInt(string(bs[j]))]
				weight := parseFloat(string(bs[j+1]))
				es[j/2] = SumEdge{
					Weight: weight,
					Node:   node,
				}
			}
			nodes[i] = &Sum{
				Edges: es,
				id:    i,
			}
		case "*":
			es := make([]PrdEdge, len(bs)-1)
			for j, v := range bs[1:] {
				es[j] = PrdEdge{
					Node: nodes[parseInt(string(v))],
				}
			}
			nodes[i] = &Prd{
				Edges: es,
				id:    i,
			}
		}
	}
	return SPN{nodes, schema}
}

func (spn SPN) EvalX(x []int) float64 {
	val := spn.Eval(X2Ass(x, spn.Schema))
	return val[len(val)-1]
}

func (spn SPN) Eval(ass [][]float64) []float64 {
	val := make([]float64, len(spn.Nodes))
	for _, n := range spn.Nodes {
		switch n := n.(type) {
		case *Trm:
			val[n.ID()] = math.Log(ass[n.Kth][n.Value])
		case *Sum:
			val[n.ID()] = logSumExpF(len(n.Edges), func(k int) float64 {
				return n.Edges[k].Weight + val[n.Edges[k].Node.ID()]
			})
		case *Prd:
			prd := 0.0
			for _, e := range n.Edges {
				prd += val[e.Node.ID()]
			}
			val[n.ID()] = prd
		}
	}
	return val
}

func (spn SPN) DerivativeX(x []int) []float64 {
	return spn.Derivative(X2Ass(x, spn.Schema))
}

func (spn SPN) Derivative(ass [][]float64) []float64 {
	pr := spn.Eval(ass)
	dr := make([]float64, len(spn.Nodes))
	for i := range dr {
		dr[i] = math.Inf(-1)
	}
	dr[len(dr)-1] = 0.0
	for i := len(spn.Nodes) - 1; i >= 0; i-- {
		switch n := spn.Nodes[i].(type) {
		case *Sum:
			for _, e := range n.Edges {
				dr[e.Node.ID()] = logSumExp(dr[e.Node.ID()], dr[i]+e.Weight)
			}
		case *Prd:
			zeroCnt := 0
			for _, e := range n.Edges {
				if math.IsInf(pr[e.Node.ID()], -1) {
					zeroCnt++
					if zeroCnt == 2 {
						break
					}
				}
			}
			for _, e := range n.Edges {
				other := 0.0
				if zeroCnt == 0 {
					other = pr[i] - pr[e.Node.ID()]
				} else if zeroCnt == 1 {
					if math.IsInf(pr[e.Node.ID()], -1) {
						for _, f := range n.Edges {
							if !math.IsInf(pr[f.Node.ID()], -1) {
								other += pr[f.Node.ID()]
							}
						}
					} else {
						other = math.Inf(-1)
					}
				} else {
					other = math.Inf(-1)
				}
				dr[e.Node.ID()] = logSumExp(dr[e.Node.ID()], dr[i]+other)
			}
		}
	}
	return dr
}

func MAP2MAX(spn SPN, q []byte) SPN {
	idMap := map[int]int{}
	varCnt := 0
	schema := make([]int, 0, len(spn.Schema))
	for i, c := range q {
		if c == '?' {
			idMap[i] = varCnt
			varCnt++
			schema = append(schema, spn.Schema[i])
		}
	}
	if varCnt == 0 {
		log.Println(string(q))
		log.Fatal("QuerySPN no '?'")
	}
	nn := len(spn.Nodes)
	ns := make([]Node, nn+1)
	we := make([]float64, nn)
	for i, n := range spn.Nodes {
		switch n := n.(type) {
		case *Trm:
			if q[n.Kth] == '?' {
				ns[i] = &Trm{Kth: idMap[n.Kth], Value: n.Value}
			} else {
				w := math.Inf(-1)
				if n.Value == 0 && (q[n.Kth] == '0' || q[n.Kth] == '*') {
					w = 0
				}
				if n.Value == 1 && (q[n.Kth] == '1' || q[n.Kth] == '*') {
					w = 0
				}
				we[i] = w
			}
		case *Sum:
			if ns[n.Edges[0].Node.ID()] == nil {
				we[i] = logSumExpF(len(n.Edges), func(k int) float64 {
					return n.Edges[k].Weight + we[n.Edges[k].Node.ID()]
				})
			} else {
				es := make([]SumEdge, len(n.Edges))
				for j, e := range n.Edges {
					es[j] = SumEdge{e.Weight + we[e.Node.ID()], ns[e.Node.ID()]}
				}
				ns[i] = &Sum{Edges: es}
			}
		case *Prd:
			es := make([]PrdEdge, 0, len(n.Edges))
			w := 0.0
			for _, e := range n.Edges {
				w += we[e.Node.ID()]
				if ns[e.Node.ID()] != nil {
					es = append(es, PrdEdge{ns[e.Node.ID()]})
				}
			}
			we[i] = w
			if len(es) > 0 {
				ns[i] = &Prd{Edges: es}
			}
		}
	}
	if _, ok := ns[nn-1].(*Sum); !ok {
		ns[nn] = &Sum{Edges: []SumEdge{{we[nn-1], ns[nn-1]}}}
	}
	nodes := make([]Node, 0, nn+1)
	for _, n := range ns {
		if n != nil {
			n.SetID(len(nodes))
			nodes = append(nodes, n)
		}
	}
	return SPN{nodes, schema}
}

func X2Ass(x []int, schema []int) [][]float64 {
	ass := make([][]float64, len(x))
	for i, xi := range x {
		ass[i] = make([]float64, schema[i])
		if xi == -1 {
			for v := 0; v < schema[i]; v++ {
				ass[i][v] = 1
			}
		} else {
			ass[i][xi] = 1
		}
	}
	return ass
}

func logSumExp(as ...float64) float64 {
	return logSumExpF(len(as), func(i int) float64 {
		return as[i]
	})
}

func logSumExpF(n int, f func(i int) float64) float64 {
	max := math.Inf(-1)
	for i := 0; i < n; i++ {
		max = math.Max(max, f(i))
	}
	if math.IsInf(max, 0) {
		return max
	}
	sum := 0.0
	for i := 0; i < n; i++ {
		sum += math.Exp(f(i) - max)
	}
	return math.Log(sum) + max
}

func parseInt(s string) int {
	r, e := strconv.ParseInt(s, 0, 0)
	if e != nil {
		log.Fatal(e)
	}
	return int(r)
}

func parseFloat(s string) float64 {
	r, e := strconv.ParseFloat(s, 64)
	if e != nil {
		log.Fatal(e)
	}
	return r
}
