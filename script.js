/* script.js - version nettoyée & optimisée
   - RenderController : rotation fluide via RAF + interpolation
   - Chargement radars async + clustering hors-DOM
   - Debounce handleRouteProgress
   - Filtrage radars le long de la route (buffer en km)
*/

/* ---------------------------
   UTILITAIRES
   --------------------------- */
function toRad(d){ return d * Math.PI / 180; }
function toDeg(r){ return r * 180 / Math.PI; }
function haversine(lat1,lon1,lat2,lon2){
  const R=6371000;
  const dLat=toRad(lat2-lat1), dLon=toRad(lon2-lon1);
  const a=Math.sin(dLat/2)**2 + Math.cos(toRad(lat1))*Math.cos(toRad(lat2))*Math.sin(dLon/2)**2;
  return R*2*Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
}
function calculateBearing(lat1,lon1,lat2,lon2){
  const y = Math.sin(toRad(lon2-lon1)) * Math.cos(toRad(lat2));
  const x = Math.cos(toRad(lat1))*Math.sin(toRad(lat2)) - Math.sin(toRad(lat1))*Math.cos(toRad(lat2))*Math.cos(toRad(lon2-lon1));
  return (toDeg(Math.atan2(y,x)) + 360) % 360;
}
function pointToSegmentDistanceKm(p, a, b){
  // p, a, b: L.LatLng or {lat,lng}
  // Return distance in km from point p to segment a-b
  // uses projection on earth surface (approx)
  const A = [a.lat, a.lng || a.lon || a.lon === 0 ? a.lon : a.lng];
  const B = [b.lat, b.lng || b.lon || b.lon === 0 ? b.lon : b.lng];
  const P = [p.lat, p.lng || p.lon || p.lon === 0 ? p.lon : p.lng];
  // project to simple Euclidean using lat/lon ~ small distance, OK for road buffers
  const ax = A[1], ay = A[0], bx = B[1], by = B[0], px = P[1], py = P[0];
  const dx = bx - ax, dy = by - ay;
  if (dx === 0 && dy === 0) return haversine(py, px, ay, ax) / 1000;
  const t = Math.max(0, Math.min(1, ((px - ax) * dx + (py - ay) * dy) / (dx*dx + dy*dy)));
  const projx = ax + t*dx, projy = ay + t*dy;
  return haversine(p[0], p[1], projy, projx) / 1000;
}

/* ---------------------------
   RENDER CONTROLLER (rotation fluide)
   --------------------------- */
/* Simple controller : garde targetAngle, currAngle, interpole au RAF.
   Applique transform: rotateZ(...) sur #map (CSS) une seule fois par frame.
   Throttle: n'applique que si diff > 0.25° pour économiser cycles.
*/
class RenderController {
  constructor(mapContainer){
    this.container = mapContainer;
    this.curr = 0; // current angle deg
    this.target = 0;
    this.running = false;
    this.lastApply = 0;
    this.ease = 0.18; // interpolation factor
    this._loop = this._loop.bind(this);
  }

  setTargetRotation(angleDeg, immediate = false){
    this.target = ((angleDeg % 360) + 360) % 360;
    if (immediate) this.curr = this.target;
    if (!this.running){ this.running = true; requestAnimationFrame(this._loop); }
  }

  _loop(){
    // Normalize difference shortest path
    let diff = ((this.target - this.curr + 540) % 360) - 180;
    if (Math.abs(diff) < 0.001){ this.running = false; return; }
    // Interpolate
    this.curr += diff * this.ease;
    // Apply only when significant to reduce style thrash
    if (Math.abs(diff) > 0.25 || (Date.now() - this.lastApply) > 200){
      // Apply transform
      // Use rotate on the map container; ensure transform-origin center
      this.container.style.transform = `rotate(${this.curr.toFixed(3)}deg)`;
      this.lastApply = Date.now();
    }
    requestAnimationFrame(this._loop);
  }

  stop(){
    this.target = 0;
    this.setTargetRotation(0, true);
  }
}

/* ---------------------------
   BASE APP STATE & MAP
   --------------------------- */

// Create map
const map = L.map('map', { zoomControl:false, attributionControl:false }).setView([46.7,2.5],6);
L.tileLayer('https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png',{maxZoom:19,attribution:''}).addTo(map);

// Use a dedicated container for RenderController (leaflet map container)
const renderController = new RenderController(map.getContainer());

// Minimal UI refs
const destInput = document.getElementById('dest');
const goBtn = document.getElementById('go');
const recenterBtn = document.getElementById('recenterBtn');
const speedEl = document.getElementById('speed');
const nextRadarHud = document.getElementById('next-radar-hud');
const nextRadarDistance = document.getElementById('next-radar-distance');
const nextRadarType = document.getElementById('next-radar-type');
const nextRadarLimit = document.getElementById('next-radar-limit');

let myMarker = null;
let accuracyCircle = null;
let myPath = [];
let lastPos = null;
let lastSpeed = null;
let lastHeading = null;
let lastValidGPSHeading = null;
let lastHighAccuracyTime = 0;

let radarsAll = [];      // all radars loaded from CSV
let radarsOnRoute = [];  // filtered for current route
let radarMarkerLayer = L.markerClusterGroup({ disableClusteringAtZoom: 12, maxClusterRadius: 60 }).addTo(map);

// routing/route
let routeCoords = [];
let routeLine = null;
let routeDistance = 0;
let currentDestination = null;
let availableRoutes = [];
let alertedIds = new Set();

/* ---------------------------
   CSV (radars) : load & process
   --------------------------- */
const CSV_URL = "https://www.data.gouv.fr/api/1/datasets/r/8a22b5a8-4b65-41be-891a-7c0aead4ba51";

async function loadRadars(){
  try {
    const res = await fetch(CSV_URL);
    if (!res.ok) throw new Error('CSV load failed');
    const txt = await res.text();
    const parsed = Papa.parse(txt, { header:true, skipEmptyLines:true }).data;
    // map + sanitize
    radarsAll = parsed.map(r=>{
      const lat = parseFloat(r.latitude || r.lat || r.Latitude || r.y || r.Y);
      const lon = parseFloat(r.longitude || r.lon || r.Longitude || r.x || r.X);
      return {
        id: (r.id || r.ID || '').toString(),
        lat, lon,
        type: (r.type || r.Type || r.equipement || '').trim(),
        route:(r.route || r.Route || '').trim(),
        ville:(r.commune || r.localisation || '').trim(),
        dep:(r.departement || r.departement_code || '').toString().trim(),
        v_vl: parseInt(r.vitesse_vehicules_legers_kmh || r.Vitesse || r.vitesse) || null,
        v_pl: parseInt(r.vitesse_poids_lourds_kmh || r.Vitesse_PL || r.vitesse_pl) || null
      };
    }).filter(rr => Number.isFinite(rr.lat) && Number.isFinite(rr.lon));
    console.log(`Radars chargés: ${radarsAll.length}`);
    // Add all radars to main layer (clustered) but keep separate layer for route markers
    const tmpLayer = L.markerClusterGroup({ disableClusteringAtZoom: 12, maxClusterRadius: 60 });
    radarsAll.forEach(e=>{
      const m = L.circleMarker([e.lat,e.lon], { radius:4, color:'#00e1ff', fill:true, fillOpacity:0.9 });
      m.bindPopup(`<b>Radar</b><br>${e.v_vl?e.v_vl+' km/h':''}`);
      m._radar = e;
      tmpLayer.addLayer(m);
    });
    // Replace global layer (single DOM operation)
    map.removeLayer(radarMarkerLayer);
    radarMarkerLayer = tmpLayer.addTo(map);
  } catch (e){
    console.error('Erreur chargement radars:', e);
  }
}

/* ---------------------------
   FILTER RADARS ALONG ROUTE
   - bufferKm: margin around route in km
   --------------------------- */
function filterRadarsAlongRoute(radars, routeCoordsArr, bufferKm = 0.5){
  if(!routeCoordsArr || routeCoordsArr.length < 2) return [];
  // Speed: precompute segment boxes to reduce checks
  const candidates = [];
  for (let r of radars){
    const p = L.latLng(r.lat, r.lon);
    // Check each segment until near enough
    let near = false;
    for (let i=1;i<routeCoordsArr.length;i++){
      const a = routeCoordsArr[i-1];
      const b = routeCoordsArr[i];
      const distKm = pointToSegmentDistanceKm(p, a, b);
      if (distKm <= bufferKm){
        near = true; break;
      }
    }
    if (near) candidates.push(r);
  }
  return candidates;
}

/* ---------------------------
   FIND NEXT RADAR ON ROUTE
   - returns { radar, distance, bearing, angleDiff } or null
   --------------------------- */
function findNextRadarOnRoute(myLatLng){
  if(!routeCoords.length || !radarsOnRoute.length) return null;
  // compute heading fallback
  const myHeading = (lastHeading !== null ? lastHeading : (lastValidGPSHeading !== null ? lastValidGPSHeading : 0));
  let candidates = [];
  const me = L.latLng(myLatLng);
  for (let r of radarsOnRoute){
    const rp = L.latLng(r.lat, r.lon);
    const d = me.distanceTo(rp); // meters
    const bearing = calculateBearing(me.lat, me.lng, r.lat, r.lon);
    let angleDiff = Math.abs(bearing - myHeading);
    if (angleDiff > 180) angleDiff = 360 - angleDiff;
    // Only ahead candidates first
    candidates.push({ radar: r, distance: d, bearing, angleDiff });
  }
  // prefer: ahead (angleDiff <= 90), sorted by distance
  const ahead = candidates.filter(c => c.angleDiff <= 90).sort((a,b)=>a.distance-b.distance);
  if (ahead.length) return ahead[0];
  // if none ahead, return nearest behind (sorted)
  candidates.sort((a,b)=>a.distance-b.distance);
  return candidates[0] || null;
}

/* ---------------------------
   Debounced handleRouteProgress
   - only runs when position changes > threshold OR every 700ms
   --------------------------- */
let _lastHandlePos = null;
let _lastHandleTime = 0;
function handleRouteProgressDebounced(currentLatLng){
  const now = Date.now();
  if (!_lastHandlePos) {
    _lastHandlePos = currentLatLng;
  }
  const moved = _lastHandlePos.distanceTo(currentLatLng) > 3; // > 3m
  if (moved || (now - _lastHandleTime) > 700){
    _lastHandlePos = currentLatLng;
    _lastHandleTime = now;
    handleRouteProgress(currentLatLng);
  }
}

function handleRouteProgress(myLatLng){
  // Update HUD only (batch DOM writes)
  const next = findNextRadarOnRoute(myLatLng);
  if (!next){
    nextRadarType.textContent = 'Aucun radar devant';
    nextRadarDistance.textContent = '—';
    nextRadarLimit.textContent = '—';
    return;
  }
  const distance = Math.round(next.distance);
  nextRadarType.textContent = next.radar.type || 'Radar';
  nextRadarDistance.textContent = distance >= 1000 ? `${(distance/1000).toFixed(1)} km` : `${distance} m`;
  nextRadarLimit.textContent = next.radar.v_vl ? `Limite: ${next.radar.v_vl} km/h` : 'Limite: —';

  // Voice + visual alert - only once per radar id
  const radarId = next.radar.id || `${next.radar.lat},${next.radar.lon}`;
  if (distance <= 1000 && !alertedIds.has(radarId)){
    alertedIds.add(radarId);
    try{ say(`Attention, ${next.radar.type || 'radar'} dans ${Math.round(next.distance)} mètres.`); }catch(e){}
    // minimal visual overlay (could be extended)
  }
}

/* ---------------------------
   GPS handling: simplified/high-precision watcher
   - filters noisy updates
   --------------------------- */
let highAccuracyWatcher = null;
let positionBuffer = [];

function setSpeedDisplay(kmh){
  if (Number.isFinite(kmh)) speedEl.textContent = `${Math.round(kmh)} km/h`; else speedEl.textContent = '—';
}

function updatePositionFromGeolocation(position){
  const now = Date.now();
  const coords = position.coords;
  if (coords.accuracy > 60) return; // ignore very imprecise positions

  // keep small buffer
  positionBuffer.push({lat:coords.latitude,lon:coords.longitude,timestamp:now,accuracy:coords.accuracy,speed:coords.speed,heading:coords.heading});
  if (positionBuffer.length > 6) positionBuffer.shift();

  // derive smoother position by averaging last 3
  const last = positionBuffer[positionBuffer.length-1];
  lastPos = {lat:last.lat, lon:last.lon, t:last.timestamp};
  // compute speed: prefer coords.speed when available
  let speedKmh = null;
  if (coords.speed !== null && coords.speed >= 0) speedKmh = coords.speed * 3.6;
  else if (positionBuffer.length >= 2){
    const prev = positionBuffer[positionBuffer.length-2];
    const d = haversine(prev.lat, prev.lon, last.lat, last.lon);
    const dt = (last.timestamp - prev.timestamp)/1000;
    if (dt > 0) speedKmh = (d/dt)*3.6;
  }
  lastSpeed = speedKmh;
  setSpeedDisplay(speedKmh);

  // heading
  if (coords.heading !== null && !Number.isNaN(coords.heading)) lastHeading = coords.heading;

  // Create marker if needed
  const latlng = [last.lat, last.lon];
  if (!myMarker){
    myMarker = L.marker(latlng).addTo(map);
    map.setView(latlng, 16);
  } else {
    // only update when moved > 0.5m to reduce layout writes
    const prev = myMarker.getLatLng();
    if (prev.distanceTo(latlng) > 0.5) myMarker.setLatLng(latlng);
  }

  // accuracy circle
  if (!accuracyCircle) {
    accuracyCircle = L.circle(latlng, {radius: coords.accuracy || 20, interactive:false}).addTo(map);
  } else {
    accuracyCircle.setLatLng(latlng);
    if ((coords.accuracy || 0) > 0) accuracyCircle.setRadius(coords.accuracy);
  }

  // track path array (light)
  myPath.push(latlng);
  if (myPath.length > 3000) myPath.shift();

  // Route progress + off-route check (debounced)
  if (routeCoords.length) {
    const me = L.latLng(latlng);
    handleRouteProgressDebounced(me);
    checkIfOffRoute(me);
  }

  lastHighAccuracyTime = Date.now();
}

/* Geo start/stop */
function startUltraHighAccuracyGeolocation(){
  if (!navigator.geolocation) { alert('Géolocalisation non supportée'); return; }
  if (highAccuracyWatcher) navigator.geolocation.clearWatch(highAccuracyWatcher);
  positionBuffer = [];
  highAccuracyWatcher = navigator.geolocation.watchPosition(updatePositionFromGeolocation, err=>{
    console.warn('Geo err', err);
  }, { enableHighAccuracy:true, maximumAge:0, timeout:7000 });
  console.log('Geo started');
}
function stopGeolocation(){
  if (highAccuracyWatcher){ navigator.geolocation.clearWatch(highAccuracyWatcher); highAccuracyWatcher = null; }
  console.log('Geo stopped');
}

/* ---------------------------
   Route calculation (abstraction)
   - simplified: use Leaflet-Routing if available else fallback to direct line
   --------------------------- */
async function calculateMultipleRoutes(originLatLng, destLatLng){
  // For robustness, attempt an OSRM call via public router if L.Routing exists
  try {
    if (window.L && L.Routing && L.Routing.osrmv1){
      return new Promise((resolve) => {
        L.Routing.control({
          waypoints:[L.latLng(originLatLng.lat,originLatLng.lng), L.latLng(destLatLng.lat,destLatLng.lng)],
          router: L.Routing.osrmv1({ serviceUrl: 'https://router.project-osrm.org/route/v1' }),
          createMarker: ()=>null,
          routeWhileDragging:false,
          fitSelectedRoute:false,
          show:false
        }).on('routesfound', function(e){
          const routes = e.routes.map((r, idx) => ({
            coords: r.coordinates.map(c => ({lat:c.lat,lng:c.lng})),
            distance: r.summary.totalDistance || r.summary.total_distance || r.summary.distance || 0,
            duration: r.summary.totalTime || r.summary.total_time || r.summary.duration || r.summary.time || 0,
            name: `Proposition ${idx+1}`,
            color: idx===0 ? '#00ffd5' : '#0088ff'
          }));
          resolve(routes);
        }).addTo(map);
      });
    } else {
      // fallback: straight line route
      return [{
        coords:[{lat:originLatLng.lat,lng:originLatLng.lng},{lat:destLatLng.lat,lng:destLatLng.lng}],
        distance: haversine(originLatLng.lat,originLatLng.lng,destLatLng.lat,destLatLng.lon || destLatLng.lng || destLatLng.lon || destLatLng.longitude) || 0,
        duration:0,
        name:'Trajet direct',
        color:'#00ffd5'
      }];
    }
  } catch(e){
    console.warn('calculateMultipleRoutes failed', e);
    return [];
  }
}

/* create route line helper */
function createEnhancedRoute(coords, color='#00ffd5'){
  const latlngs = coords.map(c=>L.latLng(c.lat, c.lng));
  const pl = L.polyline(latlngs, {color, weight:5, opacity:0.95}).addTo(map);
  return pl;
}

/* select route: apply coords, compute radarsOnRoute */
function selectRoute(route){
  if (!route || !route.coords) return;
  routeCoords = route.coords.map(c => ({lat:c.lat, lng:c.lng}));
  routeDistance = route.distance || 0;
  if (routeLine) { map.removeLayer(routeLine); routeLine = null; }
  routeLine = createEnhancedRoute(routeCoords, route.color || '#00ffd5');
  map.fitBounds(routeLine.getBounds().pad(0.1));
  // populate radarsOnRoute
  radarsOnRoute = filterRadarsAlongRoute(radarsAll, routeCoords, 1.0); // 1 km buffer to be permissive
  // replace radar markers layer with only on-route markers for clarity
  if (radarMarkerLayer) map.removeLayer(radarMarkerLayer);
  const layer = L.layerGroup();
  radarsOnRoute.forEach(r=>{
    const m = L.circleMarker([r.lat,r.lon], { radius:5, color:'#00ffa6', fill:true, fillOpacity:0.9 });
    m.bindPopup(`<b>Radar</b><br>${r.v_vl?r.v_vl+' km/h':''}`);
    m._radar = r;
    layer.addLayer(m);
  });
  radarMarkerLayer = L.markerClusterGroup({ disableClusteringAtZoom: 12, maxClusterRadius: 60 });
  radarMarkerLayer.addLayer(layer);
  radarMarkerLayer.addTo(map);
  console.log(`Radars sur route: ${radarsOnRoute.length}`);
}

/* ---------------------------
   Off-route check (simple)
   --------------------------- */
let isOffRoute = false;
let offRouteThreshold = 100; // meters

function checkIfOffRoute(currentPosition){
  if (!routeCoords.length || !currentPosition) return;
  let minDistance = Infinity;
  for (let i=1;i<routeCoords.length;i++){
    const prev = L.latLng(routeCoords[i-1]);
    const curr = L.latLng(routeCoords[i]);
    const d = pointToSegmentDistanceKm(currentPosition, prev, curr) * 1000;
    if (d < minDistance) minDistance = d;
  }
  if (minDistance > offRouteThreshold && !isOffRoute){
    isOffRoute = true;
    try { say('Vous vous éloignez de l’itinéraire — recalcul...'); }catch(e){}
    // treat recalculation (simple)
  } else if (minDistance <= offRouteThreshold){
    isOffRoute = false;
  }
}

/* ---------------------------
   Minimal TTS
   --------------------------- */
let currentUtterance = null;
function say(text){
  try {
    const u = new SpeechSynthesisUtterance(text);
    u.lang = 'fr-FR';
    u.rate = 1.0;
    speechSynthesis.cancel();
    speechSynthesis.speak(u);
    currentUtterance = u;
  } catch(e){}
}

/* ---------------------------
   Wiring UI events
   --------------------------- */
goBtn.addEventListener('click', async ()=>{
  const q = destInput.value.trim();
  if (!q) { say('Entre une destination'); return; }
  say('Recherche...');
  // quick geocode: use nominatim
  try {
    const res = await fetch(`https://nominatim.openstreetmap.org/search?format=json&q=${encodeURIComponent(q + ' France')}&limit=1`);
    const data = await res.json();
    if (!data || !data.length){ say('Destination introuvable'); return; }
    const place = data[0];
    currentDestination = L.latLng(parseFloat(place.lat), parseFloat(place.lon));
    // calculate routes
    const origin = (myMarker && myMarker.getLatLng()) ? { lat: myMarker.getLatLng().lat, lng: myMarker.getLatLng().lng } : { lat:48.86, lng:2.35 };
    const routes = await calculateMultipleRoutes(origin, {lat: currentDestination.lat, lng: currentDestination.lng});
    if (!routes.length){ say('Impossible de calculer un itinéraire'); return; }
    // choose first route automatically
    selectRoute(routes[0]);
    say('Itinéraire calculé');
  } catch(e){
    console.error('geocode error', e);
    say('Erreur recherche');
  }
});

recenterBtn.addEventListener('click', ()=>{
  if (myMarker) {
    map.setView(myMarker.getLatLng(), Math.max(map.getZoom(), 16), { animate:true });
    recenterBtn.style.display = 'none';
  }
});

/* ---------------------------
   INITIALIZATION
   --------------------------- */
(async function init(){
  // load radars first
  await loadRadars();

  // start geolocation
  startUltraHighAccuracyGeolocation();

  // Initially set rotation to 0
  renderController.setTargetRotation(0, true);

  // show recenter button when user pans
  map.on('dragstart zoomstart', ()=>{ recenterBtn.style.display = 'flex'; });

  // Debug: log when rotation requested in other code paths (keeps compatibility)
  window.renderController = renderController;

  console.log('App initialisée');
})();
