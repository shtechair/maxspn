package maxspn

import (
	"container/heap"
	"context"
	"math"
	"math/rand"
	"reflect"
	"time"
)

var ( // Main API
	_ = ApproxBT
	_ = ApproxNG
	_ = ApproxAMAP
	_ = ApproxBS
	_ = ApproxKBT
)

type XP struct {
	X []int
	P float64
}

func ApproxBT(spn SPN) []int {
	prt := make([]float64, len(spn.Nodes))
	branch := make([]int, len(spn.Nodes))
	for i, n := range spn.Nodes {
		switch n := n.(type) {
		case *Trm:
			prt[i] = 0
		case *Sum:
			eBest, pBest := -1, math.Inf(-1)
			for _, e := range n.Edges {
				crt := e.Weight + prt[e.Node.ID()]
				if pBest < crt {
					pBest = crt
					eBest = e.Node.ID()
				}
			}
			branch[i] = eBest
			prt[i] = pBest
		case *Prd:
			val := 0.0
			for _, e := range n.Edges {
				val += prt[e.Node.ID()]
			}
			prt[i] = val
		}
	}

	x := make([]int, len(spn.Schema))
	reach := make([]bool, len(spn.Nodes))
	reach[len(spn.Nodes)-1] = true
	for i := len(spn.Nodes) - 1; i >= 0; i-- {
		if reach[i] {
			switch n := spn.Nodes[i].(type) {
			case *Trm:
				x[n.Kth] = n.Value
			case *Sum:
				reach[branch[i]] = true
			case *Prd:
				for _, e := range n.Edges {
					reach[e.Node.ID()] = true
				}
			}
		}
	}
	return x
}

func ApproxNG(spn SPN) []int {
	prt := partition(spn)
	x := make([]int, len(spn.Schema))
	reach := make([]bool, len(spn.Nodes))
	reach[len(spn.Nodes)-1] = true
	for i := len(spn.Nodes) - 1; i >= 0; i-- {
		if reach[i] {
			switch n := spn.Nodes[i].(type) {
			case *Trm:
				x[n.Kth] = n.Value
			case *Sum:
				eBest, pBest := -1, math.Inf(-1)
				for _, e := range n.Edges {
					crt := e.Weight + prt[e.Node.ID()]
					if pBest < crt {
						pBest = crt
						eBest = e.Node.ID()
					}
				}
				reach[eBest] = true
			case *Prd:
				for _, e := range n.Edges {
					reach[e.Node.ID()] = true
				}
			}
		}
	}
	return x
}

func ApproxAMAP(spn SPN, timeout int) XP {
	mc := make([]XP, len(spn.Nodes))
	ctx, _ := context.WithTimeout(context.Background(), time.Duration(timeout)*time.Second)
	timeoutResult := XP{X: nil, P: math.NaN()}
	for i, n := range spn.Nodes {
		select {
		case <-ctx.Done():
			return timeoutResult
		default:
		}
		switch n := n.(type) {
		case *Trm:
			x := make([]int, len(spn.Schema))
			for xi := range x {
				x[xi] = -1
			}
			x[n.Kth] = n.Value
			mc[i] = XP{x, 0}
		case *Sum:
			xpBest := XP{nil, math.Inf(-1)}
			for _, e := range n.Edges {
				select {
				case <-ctx.Done():
					return timeoutResult
				default:
				}
				p := evalAt(spn, mc[e.Node.ID()].X, i)
				if xpBest.P < p {
					xpBest = XP{mc[e.Node.ID()].X, p}
				}
			}
			mc[i] = xpBest
		case *Prd:
			x := make([]int, len(spn.Schema))
			for xi := range x {
				x[xi] = -1
			}
			for _, e := range n.Edges {
				xe := mc[e.Node.ID()].X
				for xi := range xe {
					if xe[xi] != -1 {
						x[xi] = xe[xi]
					}
				}
			}
			mc[i] = XP{x, evalAt(spn, x, i)}
		}
	}
	return mc[len(spn.Nodes)-1]
}

func evalAt(spn SPN, x []int, at int) float64 {
	val := make([]float64, at+1)
	for i := 0; i <= at; i++ {
		n := spn.Nodes[i]
		switch n := n.(type) {
		case *Trm:
			var v float64
			if x[n.Kth] == n.Value {
				v = 0
			} else {
				v = math.Inf(-1)
			}
			val[i] = v
		case *Sum:
			val[i] = logSumExpF(len(n.Edges), func(k int) float64 {
				return n.Edges[k].Weight + val[n.Edges[k].Node.ID()]
			})
		case *Prd:
			prd := 0.0
			for _, e := range n.Edges {
				prd += val[e.Node.ID()]
			}
			val[i] = prd
		}
	}
	return val[at]
}

func ApproxBS(spn SPN, beamSize int, timeout int) float64 {
	ctx, _ := context.WithTimeout(context.Background(), time.Duration(timeout)*time.Second)
	return bs(ctx, spn, prbK(spn, beamSize), beamSize).P
}

func prbK(spn SPN, k int) []XP {
	prt := partition(spn)
	res := make([]XP, k)
	for times := 0; times < k; times++ {
		x := prb1(spn, prt)
		p := spn.EvalX(x)
		res[times] = XP{x, p}
	}
	return res
}

func partition(spn SPN) []float64 {
	ass := make([][]float64, len(spn.Schema))
	for i := range ass {
		ass[i] = make([]float64, spn.Schema[i])
		for j := range ass[i] {
			ass[i][j] = 1
		}
	}
	return spn.Eval(ass)
}

func prb1(spn SPN, prt []float64) []int {
	x := make([]int, len(spn.Schema))
	reach := make([]bool, len(spn.Nodes))
	reach[len(spn.Nodes)-1] = true
	for i := len(spn.Nodes) - 1; i >= 0; i-- {
		if reach[i] {
			switch n := spn.Nodes[i].(type) {
			case *Trm:
				x[n.Kth] = n.Value
			case *Sum:
				r := math.Log(rand.Float64()) + prt[i]
				crt := math.Inf(-1)
				for _, e := range n.Edges {
					crt = logSumExp(crt, e.Weight+prt[e.Node.ID()])
					if r < crt {
						reach[e.Node.ID()] = true
						break
					}
				}
			case *Prd:
				for _, e := range n.Edges {
					reach[e.Node.ID()] = true
				}
			}
		}
	}
	return x
}

func bs(ctx context.Context, spn SPN, xps []XP, beamSize int) XP {
	best := XP{P: math.Inf(-1)}
	for i := 0; len(xps) > 0; i++ {
		xps = uniqueX(xps)
		xps = topK(xps, beamSize)
		xp1 := topK(xps, 1)
		if best.P < xp1[0].P {
			best = xp1[0]
		}
		select {
		case <-ctx.Done():
			return best
		default:
		}
		xps = nextGens(ctx, xps, spn)
	}
	return best
}

func uniqueX(xps []XP) []XP {
	is := make([]bool, len(xps))
	res := make([]XP, 0, len(xps))
	for i, xpi := range xps {
		is[i] = true
		for j, xpj := range xps[:i] {
			if is[j] && reflect.DeepEqual(xpi.X, xpj.X) {
				is[i] = false
				break
			}
		}
		if is[i] {
			res = append(res, xpi)
		}
	}
	return res
}

func topK(xps []XP, k int) []XP {
	if k > len(xps) {
		k = len(xps)
	}
	for i := 0; i < k; i++ {
		for j := i + 1; j < len(xps); j++ {
			if xps[i].P < xps[j].P {
				xps[i], xps[j] = xps[j], xps[i]
			}
		}
	}
	return xps[:k]
}

func nextGens(ctx context.Context, xps []XP, spn SPN) []XP {
	var res []XP
	resChan := make([]chan []XP, len(xps))
	for i, xp := range xps {
		ch := make(chan []XP, 1)
		select {
		case <-ctx.Done():
		default:
			nextGenD(xp, spn, ch)
		}
		resChan[i] = ch
	}
	for _, ch := range resChan {
		res = append(res, <-ch...)
	}
	return res
}

func nextGenD(xp XP, spn SPN, ch chan []XP) {
	var res []XP
	ds := spn.DerivativeX(xp.X)
	for i, n := range spn.Nodes {
		if n, ok := n.(*Trm); ok {
			if xp.X[n.Kth] != n.Value && ds[i] > xp.P {
				nx := make([]int, len(xp.X))
				copy(nx, xp.X)
				nx[n.Kth] = n.Value
				res = append(res, XP{nx, ds[i]})
			}
		}
	}
	ch <- res
}

func ApproxKBT(spn SPN, k int, timeout int) float64 {
	xs := kbt(spn, k, timeout)
	if len(xs) == 0 {
		return math.NaN()
	}
	return maxXP(evalXBatch(spn, xs)).P
}

func kbt(spn SPN, k int, timeout int) [][]int {
	ctx, _ := context.WithTimeout(context.Background(), time.Duration(timeout)*time.Second)
	ls := make([][]*link, len(spn.Nodes))
	for i, n := range spn.Nodes {
		select {
		case <-ctx.Done():
			return nil
		default:
		}
		switch n := n.(type) {
		case *Trm:
			ls[i] = []*link{{p: 0, trm: n}}
		case *Sum:
			for _, e := range n.Edges {
				ls[i] = mergeSumLink(ls[i], ls[e.Node.ID()], 0, e.Weight, k)
			}
		case *Prd:
			for _, e := range n.Edges {
				ls[i] = mergePrdLink(ls[i], ls[e.Node.ID()], k)
			}
		}
	}
	if k > len(ls[len(spn.Nodes)-1]) {
		k = len(ls[len(spn.Nodes)-1])
	}
	xs := make([][]int, k)
	for i := range xs {
		xs[i] = make([]int, len(spn.Schema))
		dfsKBT(ls[len(spn.Nodes)-1][i], xs[i])
	}
	return xs
}

func maxXP(xps []XP) XP {
	max := XP{P: math.Inf(-1)}
	for _, xp := range xps {
		if max.P < xp.P {
			max = xp
		}
	}
	return max
}

func evalXBatch(spn SPN, xs [][]int) []XP {
	xps := make([]XP, len(xs))
	for i, x := range xs {
		xps[i] = XP{x, spn.EvalX(x)}
	}
	return xps
}

type link struct {
	p     float64
	left  *link
	right *link
	trm   *Trm
}

func dfsKBT(link *link, x []int) {
	if link.trm != nil {
		x[link.trm.Kth] = link.trm.Value
	}
	if link.left != nil {
		dfsKBT(link.left, x)
	}
	if link.right != nil {
		dfsKBT(link.right, x)
	}
}

type pairInt struct {
	left  int
	right int
}

type pairLink struct {
	p float64
	pairInt
}
type pairHeap []pairLink

func (h pairHeap) Len() int           { return len(h) }
func (h pairHeap) Less(i, j int) bool { return h[i].p > /* MaxHeap */ h[j].p }
func (h pairHeap) Swap(i, j int)      { h[i], h[j] = h[j], h[i] }
func (h *pairHeap) Push(x interface{}) {
	*h = append(*h, x.(pairLink))
}

func (h *pairHeap) Pop() interface{} {
	n := len(*h)
	r := (*h)[n-1]
	*h = (*h)[0 : n-1]
	return r
}

func mergePrdLink(left, right []*link, k int) []*link {
	if len(left) == 0 {
		return right
	}
	if len(right) == 0 {
		return left
	}

	var rs []*link
	fringe := &pairHeap{}
	heap.Init(fringe)
	set := map[pairInt]struct{}{}

	initPair := pairLink{left[0].p + right[0].p, pairInt{0, 0}}
	heap.Push(fringe, initPair)
	set[initPair.pairInt] = struct{}{}

	for len(rs) < k && fringe.Len() > 0 {
		p := heap.Pop(fringe).(pairLink)
		rs = append(rs, &link{p.p, left[p.left], right[p.right], nil})
		if p.left+1 < len(left) {
			np := pairLink{left[p.left+1].p + right[p.right].p, pairInt{p.left + 1, p.right}}
			if _, ok := set[np.pairInt]; !ok {
				heap.Push(fringe, np)
				set[np.pairInt] = struct{}{}
			}
		}
		if p.right+1 < len(right) {
			np := pairLink{left[p.left].p + right[p.right+1].p, pairInt{p.left, p.right + 1}}
			if _, ok := set[np.pairInt]; !ok {
				heap.Push(fringe, np)
				set[np.pairInt] = struct{}{}
			}
		}
	}
	return rs
}

func mergeSumLink(left, right []*link, leftWeight, rightWeight float64, k int) []*link {
	var rs []*link
	for i, j := 0, 0; i+j < k; {
		if i < len(left) && (j >= len(right) || left[i].p+leftWeight > right[j].p+rightWeight) {
			rs = append(rs, &link{p: left[i].p + leftWeight, left: left[i]})
			i++
		} else if j < len(right) {
			rs = append(rs, &link{p: right[j].p + rightWeight, right: right[j]})
			j++
		} else {
			break
		}
	}
	return rs
}
