# (C) Olli Niinivaara, 2020
# MIT Licensed

## A thread-safe generic cache with FIFO replacement policy.
## 
## Uses fine-grained locking so that individual items are locked during put or get, but
## operations targeting different keys run in parallel.
## 
## 
## A Complete Example
## ==================
##
## .. code-block:: Nim
##
##  import nichecache ; from times import epochTime
##  
##  const fibonumber = 45
##  var usecache: bool
##  var threads: array[4, Thread[void]] 
##  let cache = newNicheCache[int, int, fibonumber](-1)
##  
##  proc fibonacci(n: int): int =
##    if n <= 2: ( result = 1 ; return )
##    if not usecache: result = fibonacci(n - 1) + fibonacci(n - 2)
##    else:
##      var fibo1 = cache.get(n - 1)
##      if fibo1 == cache.nonvalue: (fibo1 = fibonacci(n - 1) ; cache.put(n - 1, fibo1))
##      var fibo2 = cache.get(n - 2)
##      if fibo2 == cache.nonvalue: (fibo2 = fibonacci(n - 2) ; cache.put(n - 2, fibo2))
##      result = fibo1 + fibo2
##    if n == fibonumber: echo fibonumber, "=", result
##  
##  proc startfibonacci() = discard fibonacci(fibonumber)
##  
##  template takeTime(code: untyped): float =
##    let epochstart = epochTime()
##    code
##    (epochTime() - epochstart) * 1000
##  
##  proc run(usingcache: bool) =
##    usecache = usingcache
##    let t = taketime:
##      for i in 0 .. threads.high:
##        createThread(threads[i], startfibonacci)
##        joinThreads(threads)
##    if usecache: echo("with cache: ", t, " ms") else: echo("without cache: ", t, " ms")
##  
##  run(true)
##  run(false)
##
##

import locks


type NicheCache*[K; V; CacheSize: static int] = ref object
  nonvalue*: V
  keys: array[CacheSize, K]
  values: array[CacheSize, V]
  locks: array[CacheSize, Lock]
  head: int
  wraplock: Lock
  wrapped: bool


proc newNicheCache*[K; V; CacheSize: static int](nonvalue: V): NicheCache[K, V, CacheSize] =
  ## Creates new NicheCache of given size.
  ## 
  ## Optimal size should be empirically determined for each application. Bigger cache means more hits, but
  ## search times are longer, especially for cache misses. Source file contains a benchmark that gives some
  ## guidelines on behaviour with different cache sizes and cache miss rates
  ## (run with: ``nim c -r --threads:on --d:release nichecache.nim``).
  ## 
  ## ``CacheSize`` must be higher than the amount of threads working on the cache.
  ## 
  ## If a key is not in cache, ``nonvalue`` will be returned.
  ## 
  ## Garbage-collectable types (string, seq, ref) cannot be used in keys or values.
  result = NicheCache[K, V, CacheSize]()
  for i in 0 ..< CacheSize:
    result.values[i] = nonvalue
    result.locks[i].initLock
  result.nonvalue = nonvalue
  result.head = CacheSize
  initLock(result.wraplock)


{.push checks:off.}

proc put*[K; V; CacheSize](cache: NicheCache[K, V, CacheSize], key: K, value: V) =
  ## Puts a new key-value pair to cache. If cache is full, oldest key gets replaced.
  ## 
  ## To delete a key, Put ``nonvalue`` as value.
  ## 
  ## To update value, just Put again - most recent value is always found first.
  ## However, old values still fill up the cache until they get replaced, so use updating sparingly.
  ## Simply put, NicheCache is not the right data structure if values need constant updating. 
  var position = cache.head.atomicDec
  if(unlikely) position < 0:
    acquire(cache.wraplock)
    position = cache.head.atomicDec
    if position < 0:
      cache.head = CacheSize - 1
      position = CacheSize - 1
      cache.wrapped = true
    release(cache.wraplock)
  acquire(cache.locks[position])
  cache.keys[position] = key
  cache.values[position] = value
  release(cache.locks[position])
  

template handle() =
  if cache.keys[i] == key:
    acquire(cache.locks[i])
    defer: release(cache.locks[i])
    if cache.keys[i] != key: return cache.nonvalue
    result = cache.values[i]
    return result


proc get*[K; V; CacheSize](cache: NicheCache[K, V, CacheSize], key: K): V =
  ## Returns the value, or ``nonvalue`` if key did not exist.
  var head = cache.head
  if(unlikely) head < 0: head = -1
  for i in head + 1 ..< CacheSize: handle()    
  if not cache.wrapped: return cache.nonvalue
  for i in 0 .. head: handle()
  return cache.nonvalue

{.pop.}

#-----------------------------------------------------------------------------------

when isMainModule and compileOption("threads"):
  import random
  from times import epochTime
  from strutils import formatFloat, FloatFormatMode

  template takeTime(code: untyped): float =
    let epochstart = epochTime()
    code
    (epochTime() - epochstart) * 1000
 
  randomize()

  const threadcount = 4
  const operationsize = 100000

  var
    cachesize: int
    inputstream: array[operationsize, int]

  let cache100 = newNicheCache[int, int, 100](-1)
  let cache10000 = newNicheCache[int, int, 10000](-1)
  let cache100000 = newNicheCache[int, int, 100000](-1)

  proc createInputstream() =  
    for i in 0 ..< cachesize: inputstream[i] = rand(int.high)
    var i = cachesize
    while i < operationsize:
      let input = rand(int.high)
      for j in i - cachesize ..< i:
        if inputstream[j] == input: continue
      inputstream[i] = input
      i.inc

  var
    cachemisspercentage: int
    operations: int
    streamposition: int
    hits: int
    misses: int
        
  template operate() =
    let middleofcache = cachesize div 2
    while (true):
      if operations >= operationsize: break
      let cachemiss = rand(100) < cachemisspercentage
      let key =
        if cachemiss: inputstream[streamposition.atomicInc]
        else:
          if streamposition < cachesize: inputstream[streamposition div 2]
          else: inputstream[streamposition - middleofcache]
      let existingvalue = cache.get(key)
      if existingvalue != cache.nonvalue:
        doAssert(existingvalue == key, "does not compute")
        hits.atomicInc
      else:
        misses.atomicInc
        cache.put(key, key)
      operations.atomicInc  

  proc operate100() =
    let cache = cache100
    {.gcsafe.}: operate()

  proc operate10000() =
    let cache = cache10000
    {.gcsafe.}: operate()

  proc operate100000() =
    let cache = cache100000
    {.gcsafe.}: operate()
  
  proc run(cs: int) =
    cachesize = cs
    operations = 0
    streamposition = 0
    hits = 0
    misses = 0
    createInputstream()
    var threads: array[threadcount, Thread[void]]
    echo ""
    echo "cachesize: ", cachesize
    let time = taketime:
      for i in 0 .. threads.high:
        if cachesize == 100: createThread(threads[i], operate100)
        elif cachesize == 10000: createThread(threads[i], operate10000)
        else: createThread(threads[i], operate100000)
      joinThreads(threads)
    echo "hits: ", hits
    echo "misses: ", misses
    echo "time: ", formatFloat(time / operations.float, ffDecimal, 5), " ms / operation"


  echo "threadcount: ", threadcount
  echo "operationsize: ", operationsize
  
  cachemisspercentage = 1
  echo "----------------------------\ncachemisses: 1%"
  run(100)
  run(10000)
  run(100000)

  cachemisspercentage = 20
  echo "----------------------------\ncachemisses: 20%"
  run(100)
  run(10000)
  run(100000)

  cachemisspercentage = 40
  echo "----------------------------\ncachemisses: 40%"
  run(100)
  run(10000)
  run(100000)

  cachemisspercentage = 90
  echo "----------------------------\ncachemisses: 90%"
  run(100)
  run(10000)
  run(100000)