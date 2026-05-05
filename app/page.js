"use client";

import { startTransition, useEffect, useRef, useState } from "react";

import certificate from "../artifacts/sample_certificate.json";
import {
  FRAME_DURATION_MS,
  VIEWBOX_SIZE,
  buildFrame,
  formatProgressPercent,
  labelPlacement,
} from "../lib/windmill-demo.js";

const DETAIL_ITEMS = [
  {
    label: "Balanced start",
    value: `${certificate.balanced_start.prev} -> ${certificate.balanced_start.curr}`,
  },
  {
    label: "Side counts",
    value: `${certificate.balanced_counts[0]} | ${certificate.balanced_counts[1]}`,
  },
  {
    label: "Cycle length",
    value: String(certificate.cycle.length),
  },
  {
    label: "Coverage",
    value: `${certificate.cover.length}/${certificate.points.length} pivots`,
  },
];

function PointMarker({ index, isPivot, isNext, projected, label, pulse }) {
  const radius = isPivot ? 14 : isNext ? 12 : 9;
  const className = isPivot ? "pivot" : isNext ? "nextPivot" : "dot";

  return (
    <g transform={`translate(${projected.x} ${projected.y})`}>
      {pulse ? <circle className="impactRing" cx="0" cy="0" r="18" /> : null}
      <circle className={className} cx="0" cy="0" r={radius} />
      <text className="pointLabel" textAnchor={label.anchor} x={label.x} y={label.y}>
        {index}
      </text>
    </g>
  );
}

function DetailStrip() {
  return (
    <section className="detailStrip" aria-label="Certificate details">
      {DETAIL_ITEMS.map((item) => (
        <div key={item.label} className="detailTile">
          <span className="detailLabel">{item.label}</span>
          <strong className="detailValue">{item.value}</strong>
        </div>
      ))}
    </section>
  );
}

export default function Page() {
  const [playing, setPlaying] = useState(true);
  const [progress, setProgress] = useState(0);
  const progressRef = useRef(progress);

  useEffect(() => {
    progressRef.current = progress;
  }, [progress]);

  useEffect(() => {
    if (!playing) {
      return undefined;
    }

    let frameId = 0;
    const startAt = performance.now() - progressRef.current * FRAME_DURATION_MS;

    const tick = (now) => {
      const nextProgress = ((now - startAt) % FRAME_DURATION_MS) / FRAME_DURATION_MS;
      progressRef.current = nextProgress;
      startTransition(() => {
        setProgress(nextProgress);
      });
      frameId = requestAnimationFrame(tick);
    };

    frameId = requestAnimationFrame(tick);
    return () => cancelAnimationFrame(frameId);
  }, [playing]);

  useEffect(() => {
    const onKeyDown = (event) => {
      if (event.code !== "Space") {
        return;
      }
      event.preventDefault();
      setPlaying((value) => !value);
    };

    window.addEventListener("keydown", onKeyDown);
    return () => window.removeEventListener("keydown", onKeyDown);
  }, []);

  const frame = buildFrame(certificate.points, certificate.cycle, progress);

  return (
    <main className="pageShell">
      <section className="heroPanel">
        <div className="copyColumn">
          <p className="eyebrow">React / Next.js windmill demo</p>
          <h1>Certified windmill motion, rendered as a live state machine.</h1>
          <p className="lede">
            The line rotates through a balanced 7-point instance. Each handoff is driven by the
            exported cycle certificate, so the animation follows a verified finite orbit instead of
            an ad hoc sketch.
          </p>

          <div className="controlRow">
            <button type="button" className="primaryButton" onClick={() => setPlaying((value) => !value)}>
              {playing ? "Pause rotation" : "Resume rotation"}
            </button>
            <div className="statusBlock" aria-live="polite">
              <span>step {frame.stepIndex + 1}/{certificate.cycle.length}</span>
              <span>pivot {frame.state.curr} -&gt; next {frame.next.curr}</span>
            </div>
          </div>

          <label className="sliderBlock">
            <span>Timeline scrub</span>
            <input
              type="range"
              min="0"
              max="1"
              step="0.001"
              value={progress}
              onChange={(event) => {
                const nextProgress = Number(event.target.value);
                setPlaying(false);
                progressRef.current = nextProgress;
                setProgress(nextProgress);
              }}
            />
            <small>{formatProgressPercent(progress)} through the repeating orbit</small>
          </label>
        </div>

        <div className="stageColumn">
          <div className="stageFrame">
            <svg
              viewBox={`0 0 ${VIEWBOX_SIZE} ${VIEWBOX_SIZE}`}
              role="img"
              aria-label="Windmill line rotating across the certified pivot cycle"
            >
              <defs>
                <linearGradient id="paperGlow" x1="0%" y1="0%" x2="100%" y2="100%">
                  <stop offset="0%" stopColor="#f8f2e7" />
                  <stop offset="100%" stopColor="#efe1cc" />
                </linearGradient>
              </defs>

              <rect className="canvasBacking" x="0" y="0" width={VIEWBOX_SIZE} height={VIEWBOX_SIZE} rx="44" />

              <line
                className="windmillLine"
                x1={frame.line.start.x}
                y1={frame.line.start.y}
                x2={frame.line.end.x}
                y2={frame.line.end.y}
              />

              {certificate.points.map((point, index) => (
                (() => {
                  const projected = frame.projectedPoints[index];
                  const label = labelPlacement(projected, frame.center);
                  const handoff =
                    (index === frame.state.curr && frame.localProgress > 0.92) ||
                    (index === frame.next.curr && frame.localProgress > 0.78);

                  return (
                <PointMarker
                  key={`${point.x}-${point.y}`}
                  index={index}
                  projected={projected}
                  label={label}
                  isPivot={index === frame.state.curr}
                  isNext={index === frame.next.curr && frame.localProgress > 0.82}
                  pulse={handoff}
                />
                  );
                })()
              ))}
            </svg>
          </div>
        </div>
      </section>

      <DetailStrip />

      <section className="summaryGrid">
        <article className="summaryBlock">
          <p className="sectionLabel">Invariant</p>
          <h2>The animation is constrained by the certificate, not by guesswork.</h2>
          <p>
            The JSON export fixes the points, the balanced start, and the exact repeating cycle.
            The React layer only interpolates between successive certified states.
          </p>
        </article>

        <article className="summaryBlock">
          <p className="sectionLabel">Artifacts</p>
          <ul className="artifactList">
            <li>
              <a href="./sample_certificate.json">Sample certificate JSON</a>
            </li>
            <li>
              <a href="./windmill_demo.gif">Original GIF render</a>
            </li>
            <li>
              <a href="../stress_report.json">Stress report</a>
            </li>
          </ul>
        </article>
      </section>
    </main>
  );
}
